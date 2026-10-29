-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:33:19.065671+00:00
-- url     : https://prove2.me/submissions/6e94f5a7-fefc-49ad-8147-311f664af67a

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
theorem collision_support_c330062_s0_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-236278927/5000000000 : ℝ)*x 0 + (5143270153/10000000000 : ℝ)*x 1 + (-291819257/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236278927/5000000000 : ℝ)^6 ≤ (1283263929393/50000000000000 : ℝ)^5 := by
    have hnat : (236278927 : ℕ)^6*50000000000000^5 ≤ 1283263929393^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236278927 5000000000 1283263929393 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143270153/10000000000 : ℝ)^6 ≤ (45028471371223/100000000000000 : ℝ)^5 := by
    have hnat : (5143270153 : ℕ)^6*100000000000000^5 ≤ 45028471371223^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143270153 10000000000 45028471371223 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (291819257/500000000 : ℝ)^6 ≤ (10481000152503/20000000000000 : ℝ)^5 := by
    have hnat : (291819257 : ℕ)^6*20000000000000^5 ≤ 10481000152503^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291819257 500000000 10481000152503 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236278927/5000000000 : ℝ), (5143270153/10000000000 : ℝ), (-291819257/500000000 : ℝ)] ![(1283263929393/50000000000000 : ℝ), (45028471371223/100000000000000 : ℝ), (10481000152503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236278927/5000000000 : ℝ)|^6 ≤ (1283263929393/50000000000000 : ℝ)^5
        have hw : |(-236278927/5000000000 : ℝ)|=(236278927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143270153/10000000000 : ℝ)|^6 ≤ (45028471371223/100000000000000 : ℝ)^5
        have hw : |(5143270153/10000000000 : ℝ)|=(5143270153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-291819257/500000000 : ℝ)|^6 ≤ (10481000152503/20000000000000 : ℝ)^5
        have hw : |(-291819257/500000000 : ℝ)|=(291819257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2571634313/5000000000 : ℝ)*x 0 + (-472547821/10000000000 : ℝ)*x 1 + (-5836392697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2571634313/5000000000 : ℝ)^6 ≤ (11257113832217/25000000000000 : ℝ)^5 := by
    have hnat : (2571634313 : ℕ)^6*25000000000000^5 ≤ 11257113832217^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571634313 5000000000 11257113832217 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472547821/10000000000 : ℝ)^6 ≤ (641615617543/25000000000000 : ℝ)^5 := by
    have hnat : (472547821 : ℕ)^6*25000000000000^5 ≤ 641615617543^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472547821 10000000000 641615617543 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5836392697/10000000000 : ℝ)^6 ≤ (26202541093921/50000000000000 : ℝ)^5 := by
    have hnat : (5836392697 : ℕ)^6*50000000000000^5 ≤ 26202541093921^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5836392697 10000000000 26202541093921 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2571634313/5000000000 : ℝ), (-472547821/10000000000 : ℝ), (-5836392697/10000000000 : ℝ)] ![(11257113832217/25000000000000 : ℝ), (641615617543/25000000000000 : ℝ), (26202541093921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2571634313/5000000000 : ℝ)|^6 ≤ (11257113832217/25000000000000 : ℝ)^5
        have hw : |(2571634313/5000000000 : ℝ)|=(2571634313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-472547821/10000000000 : ℝ)|^6 ≤ (641615617543/25000000000000 : ℝ)^5
        have hw : |(-472547821/10000000000 : ℝ)|=(472547821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5836392697/10000000000 : ℝ)|^6 ≤ (26202541093921/50000000000000 : ℝ)^5
        have hw : |(-5836392697/10000000000 : ℝ)|=(5836392697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (257163239/500000000 : ℝ)*x 0 + (5427867467/10000000000 : ℝ)*x 1 + (1082190591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257163239/500000000 : ℝ)^6 ≤ (2814275932723/6250000000000 : ℝ)^5 := by
    have hnat : (257163239 : ℕ)^6*6250000000000^5 ≤ 2814275932723^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257163239 500000000 2814275932723 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427867467/10000000000 : ℝ)^6 ≤ (48034699911419/100000000000000 : ℝ)^5 := by
    have hnat : (5427867467 : ℕ)^6*100000000000000^5 ≤ 48034699911419^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427867467 10000000000 48034699911419 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082190591/10000000000 : ℝ)^6 ≤ (6936885153553/100000000000000 : ℝ)^5 := by
    have hnat : (1082190591 : ℕ)^6*100000000000000^5 ≤ 6936885153553^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082190591 10000000000 6936885153553 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257163239/500000000 : ℝ), (5427867467/10000000000 : ℝ), (1082190591/10000000000 : ℝ)] ![(2814275932723/6250000000000 : ℝ), (48034699911419/100000000000000 : ℝ), (6936885153553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257163239/500000000 : ℝ)|^6 ≤ (2814275932723/6250000000000 : ℝ)^5
        have hw : |(257163239/500000000 : ℝ)|=(257163239/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427867467/10000000000 : ℝ)|^6 ≤ (48034699911419/100000000000000 : ℝ)^5
        have hw : |(5427867467/10000000000 : ℝ)|=(5427867467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082190591/10000000000 : ℝ)|^6 ≤ (6936885153553/100000000000000 : ℝ)^5
        have hw : |(1082190591/10000000000 : ℝ)|=(1082190591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-446584421/2500000000 : ℝ)*x 0 + (1514535173/10000000000 : ℝ)*x 1 + (-4019629277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446584421/2500000000 : ℝ)^6 ≤ (12657742955173/100000000000000 : ℝ)^5 := by
    have hnat : (446584421 : ℕ)^6*100000000000000^5 ≤ 12657742955173^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446584421 2500000000 12657742955173 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514535173/10000000000 : ℝ)^6 ≤ (10383296039459/100000000000000 : ℝ)^5 := by
    have hnat : (1514535173 : ℕ)^6*100000000000000^5 ≤ 10383296039459^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514535173 10000000000 10383296039459 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4019629277/5000000000 : ℝ)^6 ≤ (38479480492021/50000000000000 : ℝ)^5 := by
    have hnat : (4019629277 : ℕ)^6*50000000000000^5 ≤ 38479480492021^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019629277 5000000000 38479480492021 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446584421/2500000000 : ℝ), (1514535173/10000000000 : ℝ), (-4019629277/5000000000 : ℝ)] ![(12657742955173/100000000000000 : ℝ), (10383296039459/100000000000000 : ℝ), (38479480492021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446584421/2500000000 : ℝ)|^6 ≤ (12657742955173/100000000000000 : ℝ)^5
        have hw : |(-446584421/2500000000 : ℝ)|=(446584421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1514535173/10000000000 : ℝ)|^6 ≤ (10383296039459/100000000000000 : ℝ)^5
        have hw : |(1514535173/10000000000 : ℝ)|=(1514535173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4019629277/5000000000 : ℝ)|^6 ≤ (38479480492021/50000000000000 : ℝ)^5
        have hw : |(-4019629277/5000000000 : ℝ)|=(4019629277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (260807629/1000000000 : ℝ)*x 0 + (-554211859/10000000000 : ℝ)*x 1 + (-4019629449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260807629/1000000000 : ℝ)^6 ≤ (311461503133/1562500000000 : ℝ)^5 := by
    have hnat : (260807629 : ℕ)^6*1562500000000^5 ≤ 311461503133^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260807629 1000000000 311461503133 1562500000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554211859/10000000000 : ℝ)^6 ≤ (77687471407/2500000000000 : ℝ)^5 := by
    have hnat : (554211859 : ℕ)^6*2500000000000^5 ≤ 77687471407^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554211859 10000000000 77687471407 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4019629449/5000000000 : ℝ)^6 ≤ (19239741233933/25000000000000 : ℝ)^5 := by
    have hnat : (4019629449 : ℕ)^6*25000000000000^5 ≤ 19239741233933^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019629449 5000000000 19239741233933 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260807629/1000000000 : ℝ), (-554211859/10000000000 : ℝ), (-4019629449/5000000000 : ℝ)] ![(311461503133/1562500000000 : ℝ), (77687471407/2500000000000 : ℝ), (19239741233933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260807629/1000000000 : ℝ)|^6 ≤ (311461503133/1562500000000 : ℝ)^5
        have hw : |(260807629/1000000000 : ℝ)|=(260807629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-554211859/10000000000 : ℝ)|^6 ≤ (77687471407/2500000000000 : ℝ)^5
        have hw : |(-554211859/10000000000 : ℝ)|=(554211859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4019629449/5000000000 : ℝ)|^6 ≤ (19239741233933/25000000000000 : ℝ)^5
        have hw : |(-4019629449/5000000000 : ℝ)|=(4019629449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2608076659/10000000000 : ℝ)*x 0 + (93613701/125000000 : ℝ)*x 1 + (173997869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2608076659/10000000000 : ℝ)^6 ≤ (9966769792417/50000000000000 : ℝ)^5 := by
    have hnat : (2608076659 : ℕ)^6*50000000000000^5 ≤ 9966769792417^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608076659 10000000000 9966769792417 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93613701/125000000 : ℝ)^6 ≤ (8835381282171/12500000000000 : ℝ)^5 := by
    have hnat : (93613701 : ℕ)^6*12500000000000^5 ≤ 8835381282171^5*125000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93613701 125000000 8835381282171 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173997869/1250000000 : ℝ)^6 ≤ (234585253671/2500000000000 : ℝ)^5 := by
    have hnat : (173997869 : ℕ)^6*2500000000000^5 ≤ 234585253671^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173997869 1250000000 234585253671 2500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2608076659/10000000000 : ℝ), (93613701/125000000 : ℝ), (173997869/1250000000 : ℝ)] ![(9966769792417/50000000000000 : ℝ), (8835381282171/12500000000000 : ℝ), (234585253671/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2608076659/10000000000 : ℝ)|^6 ≤ (9966769792417/50000000000000 : ℝ)^5
        have hw : |(2608076659/10000000000 : ℝ)|=(2608076659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93613701/125000000 : ℝ)|^6 ≤ (8835381282171/12500000000000 : ℝ)^5
        have hw : |(93613701/125000000 : ℝ)|=(93613701/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(173997869/1250000000 : ℝ)|^6 ≤ (234585253671/2500000000000 : ℝ)^5
        have hw : |(173997869/1250000000 : ℝ)|=(173997869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (738866733/2000000000 : ℝ)*x 0 + (46274801/62500000 : ℝ)*x 1 + (-1893439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (738866733/2000000000 : ℝ)^6 ≤ (30272155180991/100000000000000 : ℝ)^5 := by
    have hnat : (738866733 : ℕ)^6*100000000000000^5 ≤ 30272155180991^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738866733 2000000000 30272155180991 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46274801/62500000 : ℝ)^6 ≤ (69720011638501/100000000000000 : ℝ)^5 := by
    have hnat : (46274801 : ℕ)^6*100000000000000^5 ≤ 69720011638501^5*62500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46274801 62500000 69720011638501 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893439/5000000000 : ℝ)^6 ≤ (3916585223/50000000000000 : ℝ)^5 := by
    have hnat : (1893439 : ℕ)^6*50000000000000^5 ≤ 3916585223^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893439 5000000000 3916585223 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(738866733/2000000000 : ℝ), (46274801/62500000 : ℝ), (-1893439/5000000000 : ℝ)] ![(30272155180991/100000000000000 : ℝ), (69720011638501/100000000000000 : ℝ), (3916585223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(738866733/2000000000 : ℝ)|^6 ≤ (30272155180991/100000000000000 : ℝ)^5
        have hw : |(738866733/2000000000 : ℝ)|=(738866733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46274801/62500000 : ℝ)|^6 ≤ (69720011638501/100000000000000 : ℝ)^5
        have hw : |(46274801/62500000 : ℝ)|=(46274801/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893439/5000000000 : ℝ)|^6 ≤ (3916585223/50000000000000 : ℝ)^5
        have hw : |(-1893439/5000000000 : ℝ)|=(1893439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-103364759/2000000000 : ℝ)*x 0 + (127405887/500000000 : ℝ)*x 1 + (-2027176951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103364759/2000000000 : ℝ)^6 ≤ (571532585669/20000000000000 : ℝ)^5 := by
    have hnat : (103364759 : ℕ)^6*20000000000000^5 ≤ 571532585669^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103364759 2000000000 571532585669 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127405887/500000000 : ℝ)^6 ≤ (1938489217691/10000000000000 : ℝ)^5 := by
    have hnat : (127405887 : ℕ)^6*10000000000000^5 ≤ 1938489217691^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127405887 500000000 1938489217691 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2027176951/2500000000 : ℝ)^6 ≤ (77757444876943/100000000000000 : ℝ)^5 := by
    have hnat : (2027176951 : ℕ)^6*100000000000000^5 ≤ 77757444876943^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027176951 2500000000 77757444876943 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103364759/2000000000 : ℝ), (127405887/500000000 : ℝ), (-2027176951/2500000000 : ℝ)] ![(571532585669/20000000000000 : ℝ), (1938489217691/10000000000000 : ℝ), (77757444876943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103364759/2000000000 : ℝ)|^6 ≤ (571532585669/20000000000000 : ℝ)^5
        have hw : |(-103364759/2000000000 : ℝ)|=(103364759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(127405887/500000000 : ℝ)|^6 ≤ (1938489217691/10000000000000 : ℝ)^5
        have hw : |(127405887/500000000 : ℝ)|=(127405887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2027176951/2500000000 : ℝ)|^6 ≤ (77757444876943/100000000000000 : ℝ)^5
        have hw : |(-2027176951/2500000000 : ℝ)|=(2027176951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (175594639/1250000000 : ℝ)*x 0 + (-89892717/500000000 : ℝ)*x 1 + (-405435323/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175594639/1250000000 : ℝ)^6 ≤ (1897367612737/20000000000000 : ℝ)^5 := by
    have hnat : (175594639 : ℕ)^6*20000000000000^5 ≤ 1897367612737^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175594639 1250000000 1897367612737 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89892717/500000000 : ℝ)^6 ≤ (3188933127007/25000000000000 : ℝ)^5 := by
    have hnat : (89892717 : ℕ)^6*25000000000000^5 ≤ 3188933127007^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89892717 500000000 3188933127007 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405435323/500000000 : ℝ)^6 ≤ (77757429411199/100000000000000 : ℝ)^5 := by
    have hnat : (405435323 : ℕ)^6*100000000000000^5 ≤ 77757429411199^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405435323 500000000 77757429411199 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175594639/1250000000 : ℝ), (-89892717/500000000 : ℝ), (-405435323/500000000 : ℝ)] ![(1897367612737/20000000000000 : ℝ), (3188933127007/25000000000000 : ℝ), (77757429411199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175594639/1250000000 : ℝ)|^6 ≤ (1897367612737/20000000000000 : ℝ)^5
        have hw : |(175594639/1250000000 : ℝ)|=(175594639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89892717/500000000 : ℝ)|^6 ≤ (3188933127007/25000000000000 : ℝ)^5
        have hw : |(-89892717/500000000 : ℝ)|=(89892717/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405435323/500000000 : ℝ)|^6 ≤ (77757429411199/100000000000000 : ℝ)^5
        have hw : |(-405435323/500000000 : ℝ)|=(405435323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (7206295627/10000000000 : ℝ)*x 0 + (2939503569/10000000000 : ℝ)*x 1 + (175751591/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7206295627/10000000000 : ℝ)^6 ≤ (2699693622571/4000000000000 : ℝ)^5 := by
    have hnat : (7206295627 : ℕ)^6*4000000000000^5 ≤ 2699693622571^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7206295627 10000000000 2699693622571 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2939503569/10000000000 : ℝ)^6 ≤ (23010644886417/100000000000000 : ℝ)^5 := by
    have hnat : (2939503569 : ℕ)^6*100000000000000^5 ≤ 23010644886417^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939503569 10000000000 23010644886417 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175751591/1250000000 : ℝ)^6 ≤ (9497014533359/100000000000000 : ℝ)^5 := by
    have hnat : (175751591 : ℕ)^6*100000000000000^5 ≤ 9497014533359^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175751591 1250000000 9497014533359 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7206295627/10000000000 : ℝ), (2939503569/10000000000 : ℝ), (175751591/1250000000 : ℝ)] ![(2699693622571/4000000000000 : ℝ), (23010644886417/100000000000000 : ℝ), (9497014533359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7206295627/10000000000 : ℝ)|^6 ≤ (2699693622571/4000000000000 : ℝ)^5
        have hw : |(7206295627/10000000000 : ℝ)|=(7206295627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2939503569/10000000000 : ℝ)|^6 ≤ (23010644886417/100000000000000 : ℝ)^5
        have hw : |(2939503569/10000000000 : ℝ)|=(2939503569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(175751591/1250000000 : ℝ)|^6 ≤ (9497014533359/100000000000000 : ℝ)^5
        have hw : |(175751591/1250000000 : ℝ)|=(175751591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (7760979413/10000000000 : ℝ)*x 0 + (163842551/500000000 : ℝ)*x 1 + (-5291779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7760979413/10000000000 : ℝ)^6 ≤ (36886703263021/50000000000000 : ℝ)^5 := by
    have hnat : (7760979413 : ℕ)^6*50000000000000^5 ≤ 36886703263021^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7760979413 10000000000 36886703263021 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163842551/500000000 : ℝ)^6 ≤ (26214889792763/100000000000000 : ℝ)^5 := by
    have hnat : (163842551 : ℕ)^6*100000000000000^5 ≤ 26214889792763^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163842551 500000000 26214889792763 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5291779/10000000000 : ℝ)^6 ≤ (11703669203/100000000000000 : ℝ)^5 := by
    have hnat : (5291779 : ℕ)^6*100000000000000^5 ≤ 11703669203^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291779 10000000000 11703669203 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7760979413/10000000000 : ℝ), (163842551/500000000 : ℝ), (-5291779/10000000000 : ℝ)] ![(36886703263021/50000000000000 : ℝ), (26214889792763/100000000000000 : ℝ), (11703669203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7760979413/10000000000 : ℝ)|^6 ≤ (36886703263021/50000000000000 : ℝ)^5
        have hw : |(7760979413/10000000000 : ℝ)|=(7760979413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163842551/500000000 : ℝ)|^6 ≤ (26214889792763/100000000000000 : ℝ)^5
        have hw : |(163842551/500000000 : ℝ)|=(163842551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5291779/10000000000 : ℝ)|^6 ≤ (11703669203/100000000000000 : ℝ)^5
        have hw : |(-5291779/10000000000 : ℝ)|=(5291779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-315863/2000000000 : ℝ)*x 0 + (3263384829/5000000000 : ℝ)*x 1 + (-233329283/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315863/2000000000 : ℝ)^6 ≤ (2742600257/100000000000000 : ℝ)^5 := by
    have hnat : (315863 : ℕ)^6*100000000000000^5 ≤ 2742600257^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315863 2000000000 2742600257 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3263384829/5000000000 : ℝ)^6 ≤ (5992912586709/10000000000000 : ℝ)^5 := by
    have hnat : (3263384829 : ℕ)^6*10000000000000^5 ≤ 5992912586709^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3263384829 5000000000 5992912586709 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233329283/500000000 : ℝ)^6 ≤ (8013626303209/20000000000000 : ℝ)^5 := by
    have hnat : (233329283 : ℕ)^6*20000000000000^5 ≤ 8013626303209^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233329283 500000000 8013626303209 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315863/2000000000 : ℝ), (3263384829/5000000000 : ℝ), (-233329283/500000000 : ℝ)] ![(2742600257/100000000000000 : ℝ), (5992912586709/10000000000000 : ℝ), (8013626303209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315863/2000000000 : ℝ)|^6 ≤ (2742600257/100000000000000 : ℝ)^5
        have hw : |(-315863/2000000000 : ℝ)|=(315863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3263384829/5000000000 : ℝ)|^6 ≤ (5992912586709/10000000000000 : ℝ)^5
        have hw : |(3263384829/5000000000 : ℝ)|=(3263384829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233329283/500000000 : ℝ)|^6 ≤ (8013626303209/20000000000000 : ℝ)^5
        have hw : |(-233329283/500000000 : ℝ)|=(233329283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1826436957/2500000000 : ℝ)*x 0 + (-390278723/5000000000 : ℝ)*x 1 + (-665492063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1826436957/2500000000 : ℝ)^6 ≤ (68611610442203/100000000000000 : ℝ)^5 := by
    have hnat : (1826436957 : ℕ)^6*100000000000000^5 ≤ 68611610442203^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826436957 2500000000 68611610442203 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390278723/5000000000 : ℝ)^6 ≤ (5858627127/125000000000 : ℝ)^5 := by
    have hnat : (390278723 : ℕ)^6*125000000000^5 ≤ 5858627127^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390278723 5000000000 5858627127 125000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (665492063/2000000000 : ℝ)^6 ≤ (2670148784029/10000000000000 : ℝ)^5 := by
    have hnat : (665492063 : ℕ)^6*10000000000000^5 ≤ 2670148784029^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665492063 2000000000 2670148784029 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1826436957/2500000000 : ℝ), (-390278723/5000000000 : ℝ), (-665492063/2000000000 : ℝ)] ![(68611610442203/100000000000000 : ℝ), (5858627127/125000000000 : ℝ), (2670148784029/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1826436957/2500000000 : ℝ)|^6 ≤ (68611610442203/100000000000000 : ℝ)^5
        have hw : |(1826436957/2500000000 : ℝ)|=(1826436957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-390278723/5000000000 : ℝ)|^6 ≤ (5858627127/125000000000 : ℝ)^5
        have hw : |(-390278723/5000000000 : ℝ)|=(390278723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-665492063/2000000000 : ℝ)|^6 ≤ (2670148784029/10000000000000 : ℝ)^5
        have hw : |(-665492063/2000000000 : ℝ)|=(665492063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1774224717/10000000000 : ℝ)*x 0 + (6897085739/10000000000 : ℝ)*x 1 + (1491133641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1774224717/10000000000 : ℝ)^6 ≤ (1255481594271/10000000000000 : ℝ)^5 := by
    have hnat : (1774224717 : ℕ)^6*10000000000000^5 ≤ 1255481594271^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774224717 10000000000 1255481594271 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6897085739/10000000000 : ℝ)^6 ≤ (12806449623059/20000000000000 : ℝ)^5 := by
    have hnat : (6897085739 : ℕ)^6*20000000000000^5 ≤ 12806449623059^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6897085739 10000000000 12806449623059 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491133641/5000000000 : ℝ)^6 ≤ (23412935934623/100000000000000 : ℝ)^5 := by
    have hnat : (1491133641 : ℕ)^6*100000000000000^5 ≤ 23412935934623^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491133641 5000000000 23412935934623 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1774224717/10000000000 : ℝ), (6897085739/10000000000 : ℝ), (1491133641/5000000000 : ℝ)] ![(1255481594271/10000000000000 : ℝ), (12806449623059/20000000000000 : ℝ), (23412935934623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1774224717/10000000000 : ℝ)|^6 ≤ (1255481594271/10000000000000 : ℝ)^5
        have hw : |(1774224717/10000000000 : ℝ)|=(1774224717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6897085739/10000000000 : ℝ)|^6 ≤ (12806449623059/20000000000000 : ℝ)^5
        have hw : |(6897085739/10000000000 : ℝ)|=(6897085739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1491133641/5000000000 : ℝ)|^6 ≤ (23412935934623/100000000000000 : ℝ)^5
        have hw : |(1491133641/5000000000 : ℝ)|=(1491133641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s0_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2031771061/2500000000 : ℝ)*x 0 + (2647903871/10000000000 : ℝ)*x 1 + (-340450791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031771061/2500000000 : ℝ)^6 ≤ (77968955073597/100000000000000 : ℝ)^5 := by
    have hnat : (2031771061 : ℕ)^6*100000000000000^5 ≤ 77968955073597^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031771061 2500000000 77968955073597 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2647903871/10000000000 : ℝ)^6 ≤ (10149687285911/50000000000000 : ℝ)^5 := by
    have hnat : (2647903871 : ℕ)^6*50000000000000^5 ≤ 10149687285911^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647903871 10000000000 10149687285911 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340450791/10000000000 : ℝ)^6 ≤ (432917583637/25000000000000 : ℝ)^5 := by
    have hnat : (340450791 : ℕ)^6*25000000000000^5 ≤ 432917583637^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340450791 10000000000 432917583637 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2031771061/2500000000 : ℝ), (2647903871/10000000000 : ℝ), (-340450791/10000000000 : ℝ)] ![(77968955073597/100000000000000 : ℝ), (10149687285911/50000000000000 : ℝ), (432917583637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2031771061/2500000000 : ℝ)|^6 ≤ (77968955073597/100000000000000 : ℝ)^5
        have hw : |(2031771061/2500000000 : ℝ)|=(2031771061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2647903871/10000000000 : ℝ)|^6 ≤ (10149687285911/50000000000000 : ℝ)^5
        have hw : |(2647903871/10000000000 : ℝ)|=(2647903871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-340450791/10000000000 : ℝ)|^6 ≤ (432917583637/25000000000000 : ℝ)^5
        have hw : |(-340450791/10000000000 : ℝ)|=(340450791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s1_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-56335441/400000000 : ℝ)*x 0 + (4944763937/10000000000 : ℝ)*x 1 + (-1345136551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56335441/400000000 : ℝ)^6 ≤ (951625450621/10000000000000 : ℝ)^5 := by
    have hnat : (56335441 : ℕ)^6*10000000000000^5 ≤ 951625450621^5*400000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56335441 400000000 951625450621 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4944763937/10000000000 : ℝ)^6 ≤ (4295113807967/10000000000000 : ℝ)^5 := by
    have hnat : (4944763937 : ℕ)^6*10000000000000^5 ≤ 4295113807967^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4944763937 10000000000 4295113807967 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345136551/2500000000 : ℝ)^6 ≤ (23766303700059/50000000000000 : ℝ)^5 := by
    have hnat : (1345136551 : ℕ)^6*50000000000000^5 ≤ 23766303700059^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345136551 2500000000 23766303700059 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56335441/400000000 : ℝ), (4944763937/10000000000 : ℝ), (-1345136551/2500000000 : ℝ)] ![(951625450621/10000000000000 : ℝ), (4295113807967/10000000000000 : ℝ), (23766303700059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56335441/400000000 : ℝ)|^6 ≤ (951625450621/10000000000000 : ℝ)^5
        have hw : |(-56335441/400000000 : ℝ)|=(56335441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4944763937/10000000000 : ℝ)|^6 ≤ (4295113807967/10000000000000 : ℝ)^5
        have hw : |(4944763937/10000000000 : ℝ)|=(4944763937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1345136551/2500000000 : ℝ)|^6 ≤ (23766303700059/50000000000000 : ℝ)^5
        have hw : |(-1345136551/2500000000 : ℝ)|=(1345136551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s1_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (77271129/156250000 : ℝ)*x 0 + (-352000209/2500000000 : ℝ)*x 1 + (-5380262337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77271129/156250000 : ℝ)^6 ≤ (4295727045037/10000000000000 : ℝ)^5 := by
    have hnat : (77271129 : ℕ)^6*10000000000000^5 ≤ 4295727045037^5*156250000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77271129 156250000 4295727045037 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352000209/2500000000 : ℝ)^6 ≤ (1189141424253/12500000000000 : ℝ)^5 := by
    have hnat : (352000209 : ℕ)^6*12500000000000^5 ≤ 1189141424253^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352000209 2500000000 1189141424253 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5380262337/10000000000 : ℝ)^6 ≤ (47529598144113/100000000000000 : ℝ)^5 := by
    have hnat : (5380262337 : ℕ)^6*100000000000000^5 ≤ 47529598144113^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380262337 10000000000 47529598144113 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(77271129/156250000 : ℝ), (-352000209/2500000000 : ℝ), (-5380262337/10000000000 : ℝ)] ![(4295727045037/10000000000000 : ℝ), (1189141424253/12500000000000 : ℝ), (47529598144113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(77271129/156250000 : ℝ)|^6 ≤ (4295727045037/10000000000000 : ℝ)^5
        have hw : |(77271129/156250000 : ℝ)|=(77271129/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-352000209/2500000000 : ℝ)|^6 ≤ (1189141424253/12500000000000 : ℝ)^5
        have hw : |(-352000209/2500000000 : ℝ)|=(352000209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5380262337/10000000000 : ℝ)|^6 ≤ (47529598144113/100000000000000 : ℝ)^5
        have hw : |(-5380262337/10000000000 : ℝ)|=(5380262337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s1_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4988177199/10000000000 : ℝ)*x 0 + (4988957411/10000000000 : ℝ)*x 1 + (923994243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4988177199/10000000000 : ℝ)^6 ≤ (10851012308661/25000000000000 : ℝ)^5 := by
    have hnat : (4988177199 : ℕ)^6*25000000000000^5 ≤ 10851012308661^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988177199 10000000000 10851012308661 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4988957411/10000000000 : ℝ)^6 ≤ (5426524508983/12500000000000 : ℝ)^5 := by
    have hnat : (4988957411 : ℕ)^6*12500000000000^5 ≤ 5426524508983^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988957411 10000000000 5426524508983 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923994243/5000000000 : ℝ)^6 ≤ (3295938670069/25000000000000 : ℝ)^5 := by
    have hnat : (923994243 : ℕ)^6*25000000000000^5 ≤ 3295938670069^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923994243 5000000000 3295938670069 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4988177199/10000000000 : ℝ), (4988957411/10000000000 : ℝ), (923994243/5000000000 : ℝ)] ![(10851012308661/25000000000000 : ℝ), (5426524508983/12500000000000 : ℝ), (3295938670069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4988177199/10000000000 : ℝ)|^6 ≤ (10851012308661/25000000000000 : ℝ)^5
        have hw : |(4988177199/10000000000 : ℝ)|=(4988177199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4988957411/10000000000 : ℝ)|^6 ≤ (5426524508983/12500000000000 : ℝ)^5
        have hw : |(4988957411/10000000000 : ℝ)|=(4988957411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(923994243/5000000000 : ℝ)|^6 ≤ (3295938670069/25000000000000 : ℝ)^5
        have hw : |(923994243/5000000000 : ℝ)|=(923994243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330062_s1_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2680316687/5000000000 : ℝ)*x 0 + (1340336121/2500000000 : ℝ)*x 1 + (-435729143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680316687/5000000000 : ℝ)^6 ≤ (23660794922069/50000000000000 : ℝ)^5 := by
    have hnat : (2680316687 : ℕ)^6*50000000000000^5 ≤ 23660794922069^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680316687 5000000000 23660794922069 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1340336121/2500000000 : ℝ)^6 ≤ (47329122827601/100000000000000 : ℝ)^5 := by
    have hnat : (1340336121 : ℕ)^6*100000000000000^5 ≤ 47329122827601^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340336121 2500000000 47329122827601 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435729143/5000000000 : ℝ)^6 ≤ (1337321827129/25000000000000 : ℝ)^5 := by
    have hnat : (435729143 : ℕ)^6*25000000000000^5 ≤ 1337321827129^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435729143 5000000000 1337321827129 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680316687/5000000000 : ℝ), (1340336121/2500000000 : ℝ), (-435729143/5000000000 : ℝ)] ![(23660794922069/50000000000000 : ℝ), (47329122827601/100000000000000 : ℝ), (1337321827129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680316687/5000000000 : ℝ)|^6 ≤ (23660794922069/50000000000000 : ℝ)^5
        have hw : |(2680316687/5000000000 : ℝ)|=(2680316687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1340336121/2500000000 : ℝ)|^6 ≤ (47329122827601/100000000000000 : ℝ)^5
        have hw : |(1340336121/2500000000 : ℝ)|=(1340336121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435729143/5000000000 : ℝ)|^6 ≤ (1337321827129/25000000000000 : ℝ)^5
        have hw : |(-435729143/5000000000 : ℝ)|=(435729143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330062 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-236278927/5000000000 : ℝ)*X 0 0+(5143270153/10000000000 : ℝ)*X 0 1+(-291819257/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2571634313/5000000000 : ℝ)*X 1 0+(-472547821/10000000000 : ℝ)*X 1 1+(-5836392697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((257163239/500000000 : ℝ)*X 2 0+(5427867467/10000000000 : ℝ)*X 2 1+(1082190591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-446584421/2500000000 : ℝ)*X 0 0+(1514535173/10000000000 : ℝ)*X 0 1+(-4019629277/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((260807629/1000000000 : ℝ)*X 1 0+(-554211859/10000000000 : ℝ)*X 1 1+(-4019629449/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2608076659/10000000000 : ℝ)*X 2 0+(93613701/125000000 : ℝ)*X 2 1+(173997869/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((738866733/2000000000 : ℝ)*X 0 0+(46274801/62500000 : ℝ)*X 0 1+(-1893439/5000000000 : ℝ)*X 0 2+(738866733/2000000000 : ℝ)*X 1 0+(46274801/62500000 : ℝ)*X 1 1+(-1893439/5000000000 : ℝ)*X 1 2+(738866733/2000000000 : ℝ)*X 2 0+(46274801/62500000 : ℝ)*X 2 1+(-1893439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-103364759/2000000000 : ℝ)*X 0 0+(127405887/500000000 : ℝ)*X 0 1+(-2027176951/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((175594639/1250000000 : ℝ)*X 1 0+(-89892717/500000000 : ℝ)*X 1 1+(-405435323/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7206295627/10000000000 : ℝ)*X 2 0+(2939503569/10000000000 : ℝ)*X 2 1+(175751591/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7760979413/10000000000 : ℝ)*X 0 0+(163842551/500000000 : ℝ)*X 0 1+(-5291779/10000000000 : ℝ)*X 0 2+(7760979413/10000000000 : ℝ)*X 1 0+(163842551/500000000 : ℝ)*X 1 1+(-5291779/10000000000 : ℝ)*X 1 2+(7760979413/10000000000 : ℝ)*X 2 0+(163842551/500000000 : ℝ)*X 2 1+(-5291779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-315863/2000000000 : ℝ)*X 0 0+(3263384829/5000000000 : ℝ)*X 0 1+(-233329283/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1826436957/2500000000 : ℝ)*X 1 0+(-390278723/5000000000 : ℝ)*X 1 1+(-665492063/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1774224717/10000000000 : ℝ)*X 2 0+(6897085739/10000000000 : ℝ)*X 2 1+(1491133641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((2031771061/2500000000 : ℝ)*X 0 0+(2647903871/10000000000 : ℝ)*X 0 1+(-340450791/10000000000 : ℝ)*X 0 2+(2031771061/2500000000 : ℝ)*X 1 0+(2647903871/10000000000 : ℝ)*X 1 1+(-340450791/10000000000 : ℝ)*X 1 2+(2031771061/2500000000 : ℝ)*X 2 0+(2647903871/10000000000 : ℝ)*X 2 1+(-340450791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((58371/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58371/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25762414403725300138029/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1227259221399/1000000000000 : ℝ)*(base7) + (104681/200000000000 : ℝ)*(base23) + (286417/500000000000 : ℝ)*(base60) + (1563971259299/1000000000000 : ℝ)*(major_s0_0) + (1563971259299/1000000000000 : ℝ)*(major_s0_1) + (1563971259299/1000000000000 : ℝ)*(major_s0_2) + (2269999/1000000000000 : ℝ)*(sp_s0_0) + (8227/4000000000 : ℝ)*(sp_s0_1) + (447495352177/250000000000 : ℝ)*(sp_s0_7) + (1789997252581/1000000000000 : ℝ)*(sp_s0_8) + (223749868029/125000000000 : ℝ)*(sp_s0_9) + (956977724511/500000000000 : ℝ)*(sp_s0_13) + (15788929/1000000000000 : ℝ)*(sp_s0_14) + (79153/500000000000 : ℝ)*(sp_s0_15) + (686696227623/1000000000000 : ℝ)*(f.failure) + (1789999467637/1000000000000 : ℝ)*(f.sum) + (3304045420097699/5000000000000000000000000000 : ℝ)*base63 + (3091407110074741/10000000000000000000000000000 : ℝ)*base65 + (7107288254925259/10000000000000000000000000000 : ℝ)*base66 + (9064310356597699/10000000000000000000000000000 : ℝ)*base69 + (14936999533189/250000000000000000000000000 : ℝ)*base70 + (825233985074741/10000000000000000000000000000 : ℝ)*base73 + (3815731730597699/10000000000000000000000000000 : ℝ)*base75 + (2702588168597699/10000000000000000000000000000 : ℝ)*base77 + (9026352925259/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (78881/100000000000000000 : ℝ)*base86 + (78881/100000000000000000 : ℝ)*base88 + (78881/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14553/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14553/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29724857545776007016529/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1221005103499/1000000000000 : ℝ)*(base7) + (541491/1000000000000 : ℝ)*(base25) + (16507/5000000000 : ℝ)*(base27) + (317653/1000000000000 : ℝ)*(base53) + (542403/1000000000000 : ℝ)*(base59) + (1519365919869/1000000000000 : ℝ)*(major_s0_0) + (1519365919869/1000000000000 : ℝ)*(major_s0_1) + (1519365602217/1000000000000 : ℝ)*(major_s0_2) + (2328577/1000000000000 : ℝ)*(sp_s0_0) + (42832877/1000000000000 : ℝ)*(sp_s0_8) + (1723687606801/1000000000000 : ℝ)*(sp_s0_14) + (1723647102501/1000000000000 : ℝ)*(sp_s0_15) + (1723689711539/1000000000000 : ℝ)*(sp_s0_16) + (472028266829/250000000000 : ℝ)*(sp_s0_20) + (667111265217/1000000000000 : ℝ)*(f.failure) + (172369025303/100000000000 : ℝ)*(f.sum) + (1054017306149843/5000000000000000000000000000 : ℝ)*base63 + (6534406068492897/10000000000000000000000000000 : ℝ)*base64 + (3288973420428629/10000000000000000000000000000 : ℝ)*base66 + (595584179329417/10000000000000000000000000000 : ℝ)*base69 + (1137374481630657/2500000000000000000000000000 : ℝ)*base70 + (3151248198428629/10000000000000000000000000000 : ℝ)*base72 + (1246597976970269/10000000000000000000000000000 : ℝ)*base75 + (1841341573029731/10000000000000000000000000000 : ℝ)*base76 + (1293274017571371/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (67401/100000000000000000 : ℝ)*base87 + (67401/100000000000000000 : ℝ)*base89 + (32599/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48681/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-48681/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35548232528414355988431/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1028253624871/1000000000000 : ℝ)*(base7) + (4242129/500000000000 : ℝ)*(base11) + (878539/1000000000000 : ℝ)*(base15) + (242083808129/1000000000000 : ℝ)*(base39) + (164737/62500000000 : ℝ)*(base50) + (753868977317/500000000000 : ℝ)*(major_s0_0) + (753868977317/500000000000 : ℝ)*(major_s0_1) + (753868977317/500000000000 : ℝ)*(major_s0_2) + (63871/100000000000 : ℝ)*(sp_s0_2) + (23537449/500000000000 : ℝ)*(sp_s0_9) + (361562829943/200000000000 : ℝ)*(sp_s0_21) + (903910877717/500000000000 : ℝ)*(sp_s0_22) + (361554984073/200000000000 : ℝ)*(sp_s0_23) + (42256484359/25000000000 : ℝ)*(sp_s0_27) + (662005749489/1000000000000 : ℝ)*(f.failure) + (1807822633973/1000000000000 : ℝ)*(f.sum) + (647796833114517/2500000000000000000000000000 : ℝ)*base63 + (2010386481471997/5000000000000000000000000000 : ℝ)*base64 + (965963863528003/5000000000000000000000000000 : ℝ)*base67 + (476234109135483/5000000000000000000000000000 : ℝ)*base68 + (3800613059813/125000000000000000000000000 : ℝ)*base71 + (3545221268528003/5000000000000000000000000000 : ℝ)*base73 + (252163923364517/5000000000000000000000000000 : ℝ)*base75 + (1949278365635483/5000000000000000000000000000 : ℝ)*base76 + (370512114528003/2500000000000000000000000000 : ℝ)*base79 + (31783/100000000000000000 : ℝ)*base86 + (31783/100000000000000000 : ℝ)*base88 + (31783/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (58371/100000 : ℝ) ^ (95/16 : ℝ) ≤ (1022669937388734963/25000000000000000000 : ℝ) := by
    have hpowers : (58371/100000 : ℝ)^95 ≤ (1022669937388734963/25000000000000000000 : ℝ)^16 := by
      have hnat : (58371 : ℕ)^95*25000000000000000000^16 ≤ 1022669937388734963^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58371 100000 1022669937388734963 25000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58371/100000 : ℝ)) (X := (1022669937388734963/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (26022669937388734963/25000000000000000000 : ℝ) ≤ (5033876141607757/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (26022669937388734963/25000000000000000000 : ℝ)^16 ≤ (5033876141607757/5000000000000000 : ℝ)^95 := by
      have hnat : (26022669937388734963 : ℕ)^16*5000000000000000^95 ≤ 5033876141607757^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26022669937388734963 25000000000000000000 5033876141607757 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5033876141607757/5000000000000000 : ℝ)) (X := (26022669937388734963/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (13522669937388734963/12500000000000000000 : ℝ) ≤ (2026665080681643/2000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (13522669937388734963/12500000000000000000 : ℝ)^16 ≤ (2026665080681643/2000000000000000 : ℝ)^95 := by
      have hnat : (13522669937388734963 : ℕ)^16*2000000000000000^95 ≤ 2026665080681643^95*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13522669937388734963 12500000000000000000 2026665080681643 2000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2026665080681643/2000000000000000 : ℝ)) (X := (13522669937388734963/12500000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(33876141607757/2918550000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(65573120192701/5837100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (58371/100000 : ℝ)) (alpha := (33876141607757/2918550000000000 : ℝ)) (beta := (65573120192701/5837100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (58371/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(33876141607757/2918550000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(65573120192701/5837100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (14553/25000 : ℝ) ^ (95/16 : ℝ) ≤ (1006240632036284677/25000000000000000000 : ℝ) := by
    have hpowers : (14553/25000 : ℝ)^95 ≤ (1006240632036284677/25000000000000000000 : ℝ)^16 := by
      have hnat : (14553 : ℕ)^95*25000000000000000000^16 ≤ 1006240632036284677^16*25000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14553 25000 1006240632036284677 25000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14553/25000 : ℝ)) (X := (1006240632036284677/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (26006240632036284677/25000000000000000000 : ℝ) ≤ (5033340739242649/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (26006240632036284677/25000000000000000000 : ℝ)^16 ≤ (5033340739242649/5000000000000000 : ℝ)^95 := by
      have hnat : (26006240632036284677 : ℕ)^16*5000000000000000^95 ≤ 5033340739242649^95*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26006240632036284677 25000000000000000000 5033340739242649 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5033340739242649/5000000000000000 : ℝ)) (X := (26006240632036284677/25000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13506240632036284677/12500000000000000000 : ℝ) ≤ (506562542500903/500000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (13506240632036284677/12500000000000000000 : ℝ)^16 ≤ (506562542500903/500000000000000 : ℝ)^95 := by
      have hnat : (13506240632036284677 : ℕ)^16*500000000000000^95 ≤ 506562542500903^95*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13506240632036284677 12500000000000000000 506562542500903 500000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (506562542500903/500000000000000 : ℝ)) (X := (13506240632036284677/12500000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(33340739242649/2910600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(10761561922127/970200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (14553/25000 : ℝ)) (alpha := (33340739242649/2910600000000000 : ℝ)) (beta := (10761561922127/970200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (14553/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(33340739242649/2910600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(10761561922127/970200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (48681/100000 : ℝ) ^ (95/16 : ℝ) ≤ (1392185086339710521/100000000000000000000 : ℝ) := by
    have hpowers : (48681/100000 : ℝ)^95 ≤ (1392185086339710521/100000000000000000000 : ℝ)^16 := by
      have hnat : (48681 : ℕ)^95*100000000000000000000^16 ≤ 1392185086339710521^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48681 100000 1392185086339710521 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48681/100000 : ℝ)) (X := (1392185086339710521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101392185086339710521/100000000000000000000 : ℝ) ≤ (5011656371952929/5000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (101392185086339710521/100000000000000000000 : ℝ)^16 ≤ (5011656371952929/5000000000000000 : ℝ)^95 := by
      have hnat : (101392185086339710521 : ℕ)^16*5000000000000000^95 ≤ 5011656371952929^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101392185086339710521 100000000000000000000 5011656371952929 5000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011656371952929/5000000000000000 : ℝ)) (X := (101392185086339710521/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51392185086339710521/50000000000000000000 : ℝ) ≤ (10046360801475011/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (51392185086339710521/50000000000000000000 : ℝ)^16 ≤ (10046360801475011/10000000000000000 : ℝ)^95 := by
      have hnat : (51392185086339710521 : ℕ)^16*10000000000000000^95 ≤ 10046360801475011^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51392185086339710521 50000000000000000000 10046360801475011 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046360801475011/10000000000000000 : ℝ)) (X := (51392185086339710521/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(3885457317643/811350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(23048057569153/4868100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (48681/100000 : ℝ)) (alpha := (3885457317643/811350000000000 : ℝ)) (beta := (23048057569153/4868100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (48681/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(3885457317643/811350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(23048057569153/4868100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-56335441/400000000 : ℝ)*X 0 0+(4944763937/10000000000 : ℝ)*X 0 1+(-1345136551/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((77271129/156250000 : ℝ)*X 1 0+(-352000209/2500000000 : ℝ)*X 1 1+(-5380262337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4988177199/10000000000 : ℝ)*X 2 0+(4988957411/10000000000 : ℝ)*X 2 1+(923994243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2680316687/5000000000 : ℝ)*X 0 0+(1340336121/2500000000 : ℝ)*X 0 1+(-435729143/5000000000 : ℝ)*X 0 2+(2680316687/5000000000 : ℝ)*X 1 0+(1340336121/2500000000 : ℝ)*X 1 1+(-435729143/5000000000 : ℝ)*X 1 2+(2680316687/5000000000 : ℝ)*X 2 0+(1340336121/2500000000 : ℝ)*X 2 1+(-435729143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330062_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-533259/50000 : ℝ) < ((-227753/100000 : ℝ)*P 0+(-227753/100000 : ℝ)*P 1+(-227753/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-533259/50000 : ℝ) < (-18090696413129769858908525882166677/1701777903210000000000000000000000 : ℝ) := by norm_num
    linear_combination (37299/1000000000000 : ℝ)*(base3) + (2047977/1000000000000 : ℝ)*(base12) + (807981/500000000000 : ℝ)*(base15) + (194721/1000000000000 : ℝ)*(base25) + (26091/31250000000 : ℝ)*(base27) + (258309348933/1000000000000 : ℝ)*(base39) + (3231622447/12500000000 : ℝ)*(base49) + (8104601/1000000000000 : ℝ)*(base60) + (227753/100000 : ℝ)*(major_s1_0) + (227753/100000 : ℝ)*(major_s1_1) + (227753/100000 : ℝ)*(major_s1_2) + (3543487455751/1000000000000 : ℝ)*(sp_s1_0) + (708697585013/200000000000 : ℝ)*(sp_s1_1) + (3543489309007/1000000000000 : ℝ)*(sp_s1_2) + (249999781947/250000000000 : ℝ)*(sp_s1_6) + (221468093983/62500000000 : ℝ)*(f.sum) + (85920071530619239/87463530000000000000000000000 : ℝ)*base63 + (39164353458799/486810000000000000000000000 : ℝ)*base64 + (3330246061193/12127500000000000000000000 : ℝ)*base67 + (21236524722137/20283750000000000000000000 : ℝ)*base69 + (73872811358680571/2367965542500000000000000000000 : ℝ)*base70 + (73248810523283/583710000000000000000000000 : ℝ)*base73 + (22285019117587/29106000000000000000000000 : ℝ)*base75 + (168838953536201/583710000000000000000000000 : ℝ)*base77 + (339061135390542581/471929535000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c330064_s0_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-2862125133/10000000000 : ℝ)*x 0 + (-697377041/2000000000 : ℝ)*x 1 + (-5562724913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2862125133/10000000000 : ℝ)^6 ≤ (22285703122399/100000000000000 : ℝ)^5 := by
    have hnat : (2862125133 : ℕ)^6*100000000000000^5 ≤ 22285703122399^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2862125133 10000000000 22285703122399 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (697377041/2000000000 : ℝ)^6 ≤ (28243933465813/100000000000000 : ℝ)^5 := by
    have hnat : (697377041 : ℕ)^6*100000000000000^5 ≤ 28243933465813^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697377041 2000000000 28243933465813 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5562724913/10000000000 : ℝ)^6 ≤ (12367590848561/25000000000000 : ℝ)^5 := by
    have hnat : (5562724913 : ℕ)^6*25000000000000^5 ≤ 12367590848561^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5562724913 10000000000 12367590848561 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2862125133/10000000000 : ℝ), (-697377041/2000000000 : ℝ), (-5562724913/10000000000 : ℝ)] ![(22285703122399/100000000000000 : ℝ), (28243933465813/100000000000000 : ℝ), (12367590848561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2862125133/10000000000 : ℝ)|^6 ≤ (22285703122399/100000000000000 : ℝ)^5
        have hw : |(-2862125133/10000000000 : ℝ)|=(2862125133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-697377041/2000000000 : ℝ)|^6 ≤ (28243933465813/100000000000000 : ℝ)^5
        have hw : |(-697377041/2000000000 : ℝ)|=(697377041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5562724913/10000000000 : ℝ)|^6 ≤ (12367590848561/25000000000000 : ℝ)^5
        have hw : |(-5562724913/10000000000 : ℝ)|=(5562724913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330064_s0_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (829219623/2500000000 : ℝ)*x 0 + (1288903299/2500000000 : ℝ)*x 1 + (-54479797/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829219623/2500000000 : ℝ)^6 ≤ (26599622588173/100000000000000 : ℝ)^5 := by
    have hnat : (829219623 : ℕ)^6*100000000000000^5 ≤ 26599622588173^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829219623 2500000000 26599622588173 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288903299/2500000000 : ℝ)^6 ≤ (4515817600747/10000000000000 : ℝ)^5 := by
    have hnat : (1288903299 : ℕ)^6*10000000000000^5 ≤ 4515817600747^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288903299 2500000000 4515817600747 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54479797/156250000 : ℝ)^6 ≤ (2824220138981/10000000000000 : ℝ)^5 := by
    have hnat : (54479797 : ℕ)^6*10000000000000^5 ≤ 2824220138981^5*156250000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54479797 156250000 2824220138981 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(829219623/2500000000 : ℝ), (1288903299/2500000000 : ℝ), (-54479797/156250000 : ℝ)] ![(26599622588173/100000000000000 : ℝ), (4515817600747/10000000000000 : ℝ), (2824220138981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(829219623/2500000000 : ℝ)|^6 ≤ (26599622588173/100000000000000 : ℝ)^5
        have hw : |(829219623/2500000000 : ℝ)|=(829219623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288903299/2500000000 : ℝ)|^6 ≤ (4515817600747/10000000000000 : ℝ)^5
        have hw : |(1288903299/2500000000 : ℝ)|=(1288903299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54479797/156250000 : ℝ)|^6 ≤ (2824220138981/10000000000000 : ℝ)^5
        have hw : |(-54479797/156250000 : ℝ)|=(54479797/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330064_s0_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (6092295789/10000000000 : ℝ)*x 0 + (-34182511/100000000 : ℝ)*x 1 + (1155870273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6092295789/10000000000 : ℝ)^6 ≤ (2758717191181/5000000000000 : ℝ)^5 := by
    have hnat : (6092295789 : ℕ)^6*5000000000000^5 ≤ 2758717191181^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6092295789 10000000000 2758717191181 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34182511/100000000 : ℝ)^6 ≤ (27578126202363/100000000000000 : ℝ)^5 := by
    have hnat : (34182511 : ℕ)^6*100000000000000^5 ≤ 27578126202363^5*100000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34182511 100000000 27578126202363 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1155870273/5000000000 : ℝ)^6 ≤ (8623764985217/50000000000000 : ℝ)^5 := by
    have hnat : (1155870273 : ℕ)^6*50000000000000^5 ≤ 8623764985217^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155870273 5000000000 8623764985217 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6092295789/10000000000 : ℝ), (-34182511/100000000 : ℝ), (1155870273/5000000000 : ℝ)] ![(2758717191181/5000000000000 : ℝ), (27578126202363/100000000000000 : ℝ), (8623764985217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6092295789/10000000000 : ℝ)|^6 ≤ (2758717191181/5000000000000 : ℝ)^5
        have hw : |(6092295789/10000000000 : ℝ)|=(6092295789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34182511/100000000 : ℝ)|^6 ≤ (27578126202363/100000000000000 : ℝ)^5
        have hw : |(-34182511/100000000 : ℝ)|=(34182511/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1155870273/5000000000 : ℝ)|^6 ≤ (8623764985217/50000000000000 : ℝ)^5
        have hw : |(1155870273/5000000000 : ℝ)|=(1155870273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330064 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (41553/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (41553/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2862125133/10000000000 : ℝ)*X 0 0+(-697377041/2000000000 : ℝ)*X 0 1+(-5562724913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((829219623/2500000000 : ℝ)*X 1 0+(1288903299/2500000000 : ℝ)*X 1 1+(-54479797/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330064_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6092295789/10000000000 : ℝ)*X 2 0+(-34182511/100000000 : ℝ)*X 2 1+(1155870273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-533259/50000 : ℝ) < ((-227753/100000 : ℝ)*P 0+(-227753/100000 : ℝ)*P 1+(-227753/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-533259/50000 : ℝ) < (-1652930665092715886020672431/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1159802236813/1000000000000 : ℝ)*(base1) + (79901186877/500000000000 : ℝ)*(base7) + (94233/500000000000 : ℝ)*(base15) + (39883/1000000000000 : ℝ)*(base33) + (857917198387/500000000000 : ℝ)*(base39) + (32765328497/40000000000 : ℝ)*(base40) + (68471/500000000000 : ℝ)*(base44) + (18029/250000000000 : ℝ)*(base50) + (854020129753/1000000000000 : ℝ)*(base60) + (2277529960117/1000000000000 : ℝ)*(major_s0_0) + (1138764931529/500000000000 : ℝ)*(major_s0_1) + (227753/100000 : ℝ)*(major_s0_2) + (1150313798177/250000000000 : ℝ)*(sp_s0_0) + (860363147651/250000000000 : ℝ)*(sp_s0_1) + (860363229003/250000000000 : ℝ)*(sp_s0_2) + (688290591179/200000000000 : ℝ)*(f.sum) + (1039914624866689/5000000000000000000000000000 : ℝ)*base63 + (91264387/1000000000000000000000 : ℝ)*base65 + (23092290037929/5000000000000000000000000000 : ℝ)*base66 + (4064292651/5000000000000000000000 : ℝ)*base69 + (4881728021672683/10000000000000000000000000000 : ℝ)*base70 + (3280572068433203/10000000000000000000000000000 : ℝ)*base73 + (1929475573866689/5000000000000000000000000000 : ℝ)*base75 + (250663167672683/10000000000000000000000000000 : ℝ)*base76 + (446415540071469/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p030_b033 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=62 ∨ c=63 ∨ c=64 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c330062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim
  · exact collision_c330064 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 62 ≤ c.val) (hhi : c.val < 65)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
