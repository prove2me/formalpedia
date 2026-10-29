-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1570_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:13.797489+00:00
-- url     : https://prove2.me/submissions/86f084a4-d5f8-4e6a-999b-af698492f17b

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1570_s0_0 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-406502179/2500000000 : ℝ)*x 0 + (5869546327/10000000000 : ℝ)*x 1 + (4879351847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406502179/2500000000 : ℝ)^4637 ≤ (2429285447587/25000000000000 : ℝ)^3613 := by
    have hnat : (406502179 : ℕ)^4637*25000000000000^3613 ≤ 2429285447587^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406502179 2500000000 2429285447587 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5869546327/10000000000 : ℝ)^4637 ≤ (1261717753313/2500000000000 : ℝ)^3613 := by
    have hnat : (5869546327 : ℕ)^4637*2500000000000^3613 ≤ 1261717753313^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5869546327 10000000000 1261717753313 2500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4879351847/10000000000 : ℝ)^4637 ≤ (39814148060859/100000000000000 : ℝ)^3613 := by
    have hnat : (4879351847 : ℕ)^4637*100000000000000^3613 ≤ 39814148060859^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4879351847 10000000000 39814148060859 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406502179/2500000000 : ℝ), (5869546327/10000000000 : ℝ), (4879351847/10000000000 : ℝ)] ![(2429285447587/25000000000000 : ℝ), (1261717753313/2500000000000 : ℝ), (39814148060859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406502179/2500000000 : ℝ)|^4637 ≤ (2429285447587/25000000000000 : ℝ)^3613
        have hw : |(-406502179/2500000000 : ℝ)|=(406502179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5869546327/10000000000 : ℝ)|^4637 ≤ (1261717753313/2500000000000 : ℝ)^3613
        have hw : |(5869546327/10000000000 : ℝ)|=(5869546327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4879351847/10000000000 : ℝ)|^4637 ≤ (39814148060859/100000000000000 : ℝ)^3613
        have hw : |(4879351847/10000000000 : ℝ)|=(4879351847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s0_1 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546547843/1000000000 : ℝ)*x 0 + (-272129017/1250000000 : ℝ)*x 1 + (4879351849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546547843/1000000000 : ℝ)^4637 ≤ (23026954987727/50000000000000 : ℝ)^3613 := by
    have hnat : (546547843 : ℕ)^4637*50000000000000^3613 ≤ 23026954987727^3613*1000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546547843 1000000000 23026954987727 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272129017/1250000000 : ℝ)^4637 ≤ (14131941924839/100000000000000 : ℝ)^3613 := by
    have hnat : (272129017 : ℕ)^4637*100000000000000^3613 ≤ 14131941924839^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272129017 1250000000 14131941924839 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4879351849/10000000000 : ℝ)^4637 ≤ (39814148081803/100000000000000 : ℝ)^3613 := by
    have hnat : (4879351849 : ℕ)^4637*100000000000000^3613 ≤ 39814148081803^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4879351849 10000000000 39814148081803 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546547843/1000000000 : ℝ), (-272129017/1250000000 : ℝ), (4879351849/10000000000 : ℝ)] ![(23026954987727/50000000000000 : ℝ), (14131941924839/100000000000000 : ℝ), (39814148081803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546547843/1000000000 : ℝ)|^4637 ≤ (23026954987727/50000000000000 : ℝ)^3613
        have hw : |(546547843/1000000000 : ℝ)|=(546547843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272129017/1250000000 : ℝ)|^4637 ≤ (14131941924839/100000000000000 : ℝ)^3613
        have hw : |(-272129017/1250000000 : ℝ)|=(272129017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4879351849/10000000000 : ℝ)|^4637 ≤ (39814148081803/100000000000000 : ℝ)^3613
        have hw : |(4879351849/10000000000 : ℝ)|=(4879351849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s0_2 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5465478487/10000000000 : ℝ)*x 0 + (2439675891/5000000000 : ℝ)*x 1 + (-2177032147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5465478487/10000000000 : ℝ)^4637 ≤ (23026955295941/50000000000000 : ℝ)^3613 := by
    have hnat : (5465478487 : ℕ)^4637*50000000000000^3613 ≤ 23026955295941^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465478487 10000000000 23026955295941 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2439675891/5000000000 : ℝ)^4637 ≤ (7962829476031/20000000000000 : ℝ)^3613 := by
    have hnat : (2439675891 : ℕ)^4637*20000000000000^3613 ≤ 7962829476031^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439675891 5000000000 7962829476031 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177032147/10000000000 : ℝ)^4637 ≤ (7065971008241/50000000000000 : ℝ)^3613 := by
    have hnat : (2177032147 : ℕ)^4637*50000000000000^3613 ≤ 7065971008241^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177032147 10000000000 7065971008241 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5465478487/10000000000 : ℝ), (2439675891/5000000000 : ℝ), (-2177032147/10000000000 : ℝ)] ![(23026955295941/50000000000000 : ℝ), (7962829476031/20000000000000 : ℝ), (7065971008241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5465478487/10000000000 : ℝ)|^4637 ≤ (23026955295941/50000000000000 : ℝ)^3613
        have hw : |(5465478487/10000000000 : ℝ)|=(5465478487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2439675891/5000000000 : ℝ)|^4637 ≤ (7962829476031/20000000000000 : ℝ)^3613
        have hw : |(2439675891/5000000000 : ℝ)|=(2439675891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2177032147/10000000000 : ℝ)|^4637 ≤ (7065971008241/50000000000000 : ℝ)^3613
        have hw : |(-2177032147/10000000000 : ℝ)|=(2177032147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s0_3 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32264459/78125000 : ℝ)*x 0 + (3093160283/10000000000 : ℝ)*x 1 + (678821969/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32264459/78125000 : ℝ)^4637 ≤ (8035670213983/25000000000000 : ℝ)^3613 := by
    have hnat : (32264459 : ℕ)^4637*25000000000000^3613 ≤ 8035670213983^3613*78125000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32264459 78125000 8035670213983 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093160283/10000000000 : ℝ)^4637 ≤ (5545130735081/25000000000000 : ℝ)^3613 := by
    have hnat : (3093160283 : ℕ)^4637*25000000000000^3613 ≤ 5545130735081^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093160283 10000000000 5545130735081 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678821969/1250000000 : ℝ)^4637 ≤ (22838398095899/50000000000000 : ℝ)^3613 := by
    have hnat : (678821969 : ℕ)^4637*50000000000000^3613 ≤ 22838398095899^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678821969 1250000000 22838398095899 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32264459/78125000 : ℝ), (3093160283/10000000000 : ℝ), (678821969/1250000000 : ℝ)] ![(8035670213983/25000000000000 : ℝ), (5545130735081/25000000000000 : ℝ), (22838398095899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32264459/78125000 : ℝ)|^4637 ≤ (8035670213983/25000000000000 : ℝ)^3613
        have hw : |(32264459/78125000 : ℝ)|=(32264459/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093160283/10000000000 : ℝ)|^4637 ≤ (5545130735081/25000000000000 : ℝ)^3613
        have hw : |(3093160283/10000000000 : ℝ)|=(3093160283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678821969/1250000000 : ℝ)|^4637 ≤ (22838398095899/50000000000000 : ℝ)^3613
        have hw : |(678821969/1250000000 : ℝ)|=(678821969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s0_4 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1629061157/10000000000 : ℝ)*x 0 + (4904307149/10000000000 : ℝ)*x 1 + (5843708861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1629061157/10000000000 : ℝ)^4637 ≤ (4870279834479/50000000000000 : ℝ)^3613 := by
    have hnat : (1629061157 : ℕ)^4637*50000000000000^3613 ≤ 4870279834479^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629061157 10000000000 4870279834479 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4904307149/10000000000 : ℝ)^4637 ≤ (40075678066669/100000000000000 : ℝ)^3613 := by
    have hnat : (4904307149 : ℕ)^4637*100000000000000^3613 ≤ 40075678066669^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4904307149 10000000000 40075678066669 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5843708861/10000000000 : ℝ)^4637 ≤ (10036752449383/20000000000000 : ℝ)^3613 := by
    have hnat : (5843708861 : ℕ)^4637*20000000000000^3613 ≤ 10036752449383^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5843708861 10000000000 10036752449383 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1629061157/10000000000 : ℝ), (4904307149/10000000000 : ℝ), (5843708861/10000000000 : ℝ)] ![(4870279834479/50000000000000 : ℝ), (40075678066669/100000000000000 : ℝ), (10036752449383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1629061157/10000000000 : ℝ)|^4637 ≤ (4870279834479/50000000000000 : ℝ)^3613
        have hw : |(-1629061157/10000000000 : ℝ)|=(1629061157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4904307149/10000000000 : ℝ)|^4637 ≤ (40075678066669/100000000000000 : ℝ)^3613
        have hw : |(4904307149/10000000000 : ℝ)|=(4904307149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5843708861/10000000000 : ℝ)|^4637 ≤ (10036752449383/20000000000000 : ℝ)^3613
        have hw : |(5843708861/10000000000 : ℝ)|=(5843708861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s0_5 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207791171/400000000 : ℝ)*x 0 + (-1212679649/10000000000 : ℝ)*x 1 + (730463813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207791171/400000000 : ℝ)^4637 ≤ (21573611424259/50000000000000 : ℝ)^3613 := by
    have hnat : (207791171 : ℕ)^4637*50000000000000^3613 ≤ 21573611424259^3613*400000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207791171 400000000 21573611424259 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212679649/10000000000 : ℝ)^4637 ≤ (1333799357687/20000000000000 : ℝ)^3613 := by
    have hnat : (1212679649 : ℕ)^4637*20000000000000^3613 ≤ 1333799357687^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212679649 10000000000 1333799357687 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730463813/1250000000 : ℝ)^4637 ≤ (50183780355369/100000000000000 : ℝ)^3613 := by
    have hnat : (730463813 : ℕ)^4637*100000000000000^3613 ≤ 50183780355369^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730463813 1250000000 50183780355369 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207791171/400000000 : ℝ), (-1212679649/10000000000 : ℝ), (730463813/1250000000 : ℝ)] ![(21573611424259/50000000000000 : ℝ), (1333799357687/20000000000000 : ℝ), (50183780355369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207791171/400000000 : ℝ)|^4637 ≤ (21573611424259/50000000000000 : ℝ)^3613
        have hw : |(207791171/400000000 : ℝ)|=(207791171/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1212679649/10000000000 : ℝ)|^4637 ≤ (1333799357687/20000000000000 : ℝ)^3613
        have hw : |(-1212679649/10000000000 : ℝ)|=(1212679649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(730463813/1250000000 : ℝ)|^4637 ≤ (50183780355369/100000000000000 : ℝ)^3613
        have hw : |(730463813/1250000000 : ℝ)|=(730463813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s0_6 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298696557/2500000000 : ℝ)*x 0 + (730463197/1250000000 : ℝ)*x 1 + (-1212676843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298696557/2500000000 : ℝ)^4637 ≤ (10786824241779/25000000000000 : ℝ)^3613 := by
    have hnat : (1298696557 : ℕ)^4637*25000000000000^3613 ≤ 10786824241779^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298696557 2500000000 10786824241779 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730463197/1250000000 : ℝ)^4637 ≤ (25091863020517/50000000000000 : ℝ)^3613 := by
    have hnat : (730463197 : ℕ)^4637*50000000000000^3613 ≤ 25091863020517^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730463197 1250000000 25091863020517 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1212676843/10000000000 : ℝ)^4637 ≤ (6668976983607/100000000000000 : ℝ)^3613 := by
    have hnat : (1212676843 : ℕ)^4637*100000000000000^3613 ≤ 6668976983607^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212676843 10000000000 6668976983607 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298696557/2500000000 : ℝ), (730463197/1250000000 : ℝ), (-1212676843/10000000000 : ℝ)] ![(10786824241779/25000000000000 : ℝ), (25091863020517/50000000000000 : ℝ), (6668976983607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298696557/2500000000 : ℝ)|^4637 ≤ (10786824241779/25000000000000 : ℝ)^3613
        have hw : |(1298696557/2500000000 : ℝ)|=(1298696557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(730463197/1250000000 : ℝ)|^4637 ≤ (25091863020517/50000000000000 : ℝ)^3613
        have hw : |(730463197/1250000000 : ℝ)|=(730463197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1212676843/10000000000 : ℝ)|^4637 ≤ (6668976983607/100000000000000 : ℝ)^3613
        have hw : |(-1212676843/10000000000 : ℝ)|=(1212676843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s0_7 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4137061099/10000000000 : ℝ)*x 0 + (268583573/500000000 : ℝ)*x 1 + (1577074143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4137061099/10000000000 : ℝ)^4637 ≤ (32214721971883/100000000000000 : ℝ)^3613 := by
    have hnat : (4137061099 : ℕ)^4637*100000000000000^3613 ≤ 32214721971883^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137061099 10000000000 32214721971883 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268583573/500000000 : ℝ)^4637 ≤ (45041909792353/100000000000000 : ℝ)^3613 := by
    have hnat : (268583573 : ℕ)^4637*100000000000000^3613 ≤ 45041909792353^3613*500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268583573 500000000 45041909792353 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577074143/5000000000 : ℝ)^4637 ≤ (22743368219411/100000000000000 : ℝ)^3613 := by
    have hnat : (1577074143 : ℕ)^4637*100000000000000^3613 ≤ 22743368219411^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577074143 5000000000 22743368219411 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4137061099/10000000000 : ℝ), (268583573/500000000 : ℝ), (1577074143/5000000000 : ℝ)] ![(32214721971883/100000000000000 : ℝ), (45041909792353/100000000000000 : ℝ), (22743368219411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4137061099/10000000000 : ℝ)|^4637 ≤ (32214721971883/100000000000000 : ℝ)^3613
        have hw : |(4137061099/10000000000 : ℝ)|=(4137061099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268583573/500000000 : ℝ)|^4637 ≤ (45041909792353/100000000000000 : ℝ)^3613
        have hw : |(268583573/500000000 : ℝ)|=(268583573/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577074143/5000000000 : ℝ)|^4637 ≤ (22743368219411/100000000000000 : ℝ)^3613
        have hw : |(1577074143/5000000000 : ℝ)|=(1577074143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1570_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (443/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (0 : ℝ) ^ (4635/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4635 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4635*1^1024 ≤ 0^1024*1^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4635/1024 : ℝ) ≤ (98777361093217099/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4635 ≤ (98777361093217099/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4635*6250000000000000000^1024 ≤ 98777361093217099^1024*5^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 98777361093217099 6250000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (98777361093217099/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4635 := by
      have hnat : (1 : ℕ)^1024*1^4635 ≤ 1^4635*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6348777361093217099/6250000000000000000 : ℝ) ≤ (10034703287301703/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (6348777361093217099/6250000000000000000 : ℝ)^1024 ≤ (10034703287301703/10000000000000000 : ℝ)^4635 := by
      have hnat : (6348777361093217099 : ℕ)^1024*10000000000000000^4635 ≤ 10034703287301703^4635*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6348777361093217099 6250000000000000000 10034703287301703 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034703287301703/10000000000000000 : ℝ)) (X := (6348777361093217099/6250000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3223777361093217099/3125000000000000000 : ℝ) ≤ (5034703287301703/5000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (3223777361093217099/3125000000000000000 : ℝ)^1024 ≤ (5034703287301703/5000000000000000 : ℝ)^4635 := by
      have hnat : (3223777361093217099 : ℕ)^1024*5000000000000000^4635 ≤ 5034703287301703^4635*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3223777361093217099 3125000000000000000 5034703287301703 5000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5034703287301703/5000000000000000 : ℝ)) (X := (3223777361093217099/3125000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(34703287301703/4000000000000000 : ℝ)*(0 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34703287301703/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(98777361093217099/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(34703287301703/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4635/1024 : ℝ) := by
    rw [show (1 : ℝ)+(34703287301703/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10034703287301703/10000000000000000 : ℝ) by norm_num, show 1+(98777361093217099/6250000000000000000 : ℝ)+(0 : ℝ)=(6348777361093217099/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(98777361093217099/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(34703287301703/4000000000000000 : ℝ)*(2/5 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34703287301703/4000000000000000 : ℝ)*(2/5 : ℝ)=(5034703287301703/5000000000000000 : ℝ) by norm_num, show 1+2*(98777361093217099/6250000000000000000 : ℝ)=(3223777361093217099/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(34703287301703/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34703287301703/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(34703287301703/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34703287301703/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(34703287301703/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34703287301703/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-406502179/2500000000 : ℝ)*X 0 0+(5869546327/10000000000 : ℝ)*X 0 1+(4879351847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((546547843/1000000000 : ℝ)*X 1 0+(-272129017/1250000000 : ℝ)*X 1 1+(4879351849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5465478487/10000000000 : ℝ)*X 2 0+(2439675891/5000000000 : ℝ)*X 2 1+(-2177032147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((32264459/78125000 : ℝ)*X 0 0+(3093160283/10000000000 : ℝ)*X 0 1+(678821969/1250000000 : ℝ)*X 0 2+(32264459/78125000 : ℝ)*X 1 0+(3093160283/10000000000 : ℝ)*X 1 1+(678821969/1250000000 : ℝ)*X 1 2+(32264459/78125000 : ℝ)*X 2 0+(3093160283/10000000000 : ℝ)*X 2 1+(678821969/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1629061157/10000000000 : ℝ)*X 0 0+(4904307149/10000000000 : ℝ)*X 0 1+(5843708861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((207791171/400000000 : ℝ)*X 1 0+(-1212679649/10000000000 : ℝ)*X 1 1+(730463813/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1298696557/2500000000 : ℝ)*X 2 0+(730463197/1250000000 : ℝ)*X 2 1+(-1212676843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4137061099/10000000000 : ℝ)*X 0 0+(268583573/500000000 : ℝ)*X 0 1+(1577074143/5000000000 : ℝ)*X 0 2+(4137061099/10000000000 : ℝ)*X 1 0+(268583573/500000000 : ℝ)*X 1 1+(1577074143/5000000000 : ℝ)*X 1 2+(4137061099/10000000000 : ℝ)*X 2 0+(268583573/500000000 : ℝ)*X 2 1+(1577074143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (207555178286902618486971/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77732397/100000000000000 : ℝ)*(base1) + (431737421/25000000000000 : ℝ)*(base19) + (1737482167/100000000000000 : ℝ)*(base23) + (56313733/25000000000000 : ℝ)*(upper3) + (56234127/25000000000000 : ℝ)*(upper5) + (359435930481119/50000000000000 : ℝ)*(major0) + (359435930481119/50000000000000 : ℝ)*(major1) + (359435930481119/50000000000000 : ℝ)*(major2) + (1009908722129343/100000000000000 : ℝ)*(sp0) + (1009913360381167/100000000000000 : ℝ)*(sp1) + (252478337462171/25000000000000 : ℝ)*(sp2) + (213912772859287/50000000000000 : ℝ)*(sp3) + (402683369/6250000000000 : ℝ)*(sp4) + (2734402411/100000000000000 : ℝ)*(sp7) + (213914178926691/50000000000000 : ℝ)*(f.failure) + (1009915087330851/100000000000000 : ℝ)*(f.sum) + (65933584054343/100000000000000000000000000000 : ℝ)*base66 + (1153195773754343/200000000000000000000000000000 : ℝ)*base68 + (71208913754343/200000000000000000000000000000 : ℝ)*base70 + (1098908931354343/200000000000000000000000000000 : ℝ)*base72 + (315518280954343/100000000000000000000000000000 : ℝ)*base74 + (1144040497354343/200000000000000000000000000000 : ℝ)*base76 + (1557015590954343/200000000000000000000000000000 : ℝ)*base78 + (1345096179954343/200000000000000000000000000000 : ℝ)*base80 + (157603033445657/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (280171/50000000000000000000 : ℝ)*base89 + (280171/50000000000000000000 : ℝ)*base91 + (280171/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66132947037369106103697/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206002541/50000000000000 : ℝ)*(base15) + (6102393/25000000000000 : ℝ)*(base23) + (377647939/100000000000000 : ℝ)*(base51) + (75924847/50000000000000 : ℝ)*(upper4) + (1614859/2500000000000 : ℝ)*(upper5) + (378867385868689/50000000000000 : ℝ)*(major0) + (378867385868689/50000000000000 : ℝ)*(major1) + (378867385868689/50000000000000 : ℝ)*(major2) + (341494211/50000000000000 : ℝ)*(sp0) + (53685673/4000000000000 : ℝ)*(sp3) + (532255821064499/50000000000000 : ℝ)*(sp4) + (532255956556169/50000000000000 : ℝ)*(sp5) + (1064512300707847/100000000000000 : ℝ)*(sp6) + (45095583212687/10000000000000 : ℝ)*(sp7) + (90191434853739/20000000000000 : ℝ)*(f.failure) + (53225616255871/5000000000000 : ℝ)*(f.sum) + (180367914877367/100000000000000000000000000000 : ℝ)*base65 + (1460299609877367/200000000000000000000000000000 : ℝ)*base67 + (241991697677367/200000000000000000000000000000 : ℝ)*base69 + (732453988077367/200000000000000000000000000000 : ℝ)*base71 + (547813752777367/100000000000000000000000000000 : ℝ)*base73 + (238065369677367/200000000000000000000000000000 : ℝ)*base75 + (1920866754877367/200000000000000000000000000000 : ℝ)*base77 + (2249175174677367/200000000000000000000000000000 : ℝ)*base79 + (8620964177367/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (179341/20000000000000000000 : ℝ)*base90 + (179341/20000000000000000000 : ℝ)*base92 + (179341/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1570_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1570_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1570_s1_0 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220577/1250000 : ℝ)*x 0 + (2767414591/5000000000 : ℝ)*x 1 + (5124729373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220577/1250000 : ℝ)^4637 ≤ (10792823573793/100000000000000 : ℝ)^3613 := by
    have hnat : (220577 : ℕ)^4637*100000000000000^3613 ≤ 10792823573793^3613*1250000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220577 1250000 10792823573793 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2767414591/5000000000 : ℝ)^4637 ≤ (23402624983699/50000000000000 : ℝ)^3613 := by
    have hnat : (2767414591 : ℕ)^4637*50000000000000^3613 ≤ 23402624983699^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767414591 5000000000 23402624983699 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5124729373/10000000000 : ℝ)^4637 ≤ (42401926445343/100000000000000 : ℝ)^3613 := by
    have hnat : (5124729373 : ℕ)^4637*100000000000000^3613 ≤ 42401926445343^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124729373 10000000000 42401926445343 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220577/1250000 : ℝ), (2767414591/5000000000 : ℝ), (5124729373/10000000000 : ℝ)] ![(10792823573793/100000000000000 : ℝ), (23402624983699/50000000000000 : ℝ), (42401926445343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220577/1250000 : ℝ)|^4637 ≤ (10792823573793/100000000000000 : ℝ)^3613
        have hw : |(-220577/1250000 : ℝ)|=(220577/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2767414591/5000000000 : ℝ)|^4637 ≤ (23402624983699/50000000000000 : ℝ)^3613
        have hw : |(2767414591/5000000000 : ℝ)|=(2767414591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5124729373/10000000000 : ℝ)|^4637 ≤ (42401926445343/100000000000000 : ℝ)^3613
        have hw : |(5124729373/10000000000 : ℝ)|=(5124729373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s1_1 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376436917/10000000000 : ℝ)*x 0 + (-494781619/2500000000 : ℝ)*x 1 + (5124729121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376436917/10000000000 : ℝ)^4637 ≤ (22546600069063/50000000000000 : ℝ)^3613 := by
    have hnat : (5376436917 : ℕ)^4637*50000000000000^3613 ≤ 22546600069063^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376436917 10000000000 22546600069063 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494781619/2500000000 : ℝ)^4637 ≤ (500195043397/4000000000000 : ℝ)^3613 := by
    have hnat : (494781619 : ℕ)^4637*4000000000000^3613 ≤ 500195043397^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494781619 2500000000 500195043397 4000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5124729121/10000000000 : ℝ)^4637 ≤ (21200961884677/50000000000000 : ℝ)^3613 := by
    have hnat : (5124729121 : ℕ)^4637*50000000000000^3613 ≤ 21200961884677^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124729121 10000000000 21200961884677 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376436917/10000000000 : ℝ), (-494781619/2500000000 : ℝ), (5124729121/10000000000 : ℝ)] ![(22546600069063/50000000000000 : ℝ), (500195043397/4000000000000 : ℝ), (21200961884677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376436917/10000000000 : ℝ)|^4637 ≤ (22546600069063/50000000000000 : ℝ)^3613
        have hw : |(5376436917/10000000000 : ℝ)|=(5376436917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-494781619/2500000000 : ℝ)|^4637 ≤ (500195043397/4000000000000 : ℝ)^3613
        have hw : |(-494781619/2500000000 : ℝ)|=(494781619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5124729121/10000000000 : ℝ)|^4637 ≤ (21200961884677/50000000000000 : ℝ)^3613
        have hw : |(5124729121/10000000000 : ℝ)|=(5124729121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s1_2 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376436823/10000000000 : ℝ)*x 0 + (1281182367/2500000000 : ℝ)*x 1 + (-989563073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376436823/10000000000 : ℝ)^4637 ≤ (22546599563141/50000000000000 : ℝ)^3613 := by
    have hnat : (5376436823 : ℕ)^4637*50000000000000^3613 ≤ 22546599563141^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376436823 10000000000 22546599563141 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281182367/2500000000 : ℝ)^4637 ≤ (42401927454149/100000000000000 : ℝ)^3613 := by
    have hnat : (1281182367 : ℕ)^4637*100000000000000^3613 ≤ 42401927454149^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281182367 2500000000 42401927454149 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (989563073/5000000000 : ℝ)^4637 ≤ (3126218352227/25000000000000 : ℝ)^3613 := by
    have hnat : (989563073 : ℕ)^4637*25000000000000^3613 ≤ 3126218352227^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989563073 5000000000 3126218352227 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376436823/10000000000 : ℝ), (1281182367/2500000000 : ℝ), (-989563073/5000000000 : ℝ)] ![(22546599563141/50000000000000 : ℝ), (42401927454149/100000000000000 : ℝ), (3126218352227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376436823/10000000000 : ℝ)|^4637 ≤ (22546599563141/50000000000000 : ℝ)^3613
        have hw : |(5376436823/10000000000 : ℝ)|=(5376436823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281182367/2500000000 : ℝ)|^4637 ≤ (42401927454149/100000000000000 : ℝ)^3613
        have hw : |(1281182367/2500000000 : ℝ)|=(1281182367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-989563073/5000000000 : ℝ)|^4637 ≤ (3126218352227/25000000000000 : ℝ)^3613
        have hw : |(-989563073/5000000000 : ℝ)|=(989563073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s1_3 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (845692097/2000000000 : ℝ)*x 0 + (1883379593/5000000000 : ℝ)*x 1 + (4734826743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845692097/2000000000 : ℝ)^4637 ≤ (16565497959627/50000000000000 : ℝ)^3613 := by
    have hnat : (845692097 : ℕ)^4637*50000000000000^3613 ≤ 16565497959627^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845692097 2000000000 16565497959627 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1883379593/5000000000 : ℝ)^4637 ≤ (14280988015369/50000000000000 : ℝ)^3613 := by
    have hnat : (1883379593 : ℕ)^4637*50000000000000^3613 ≤ 14280988015369^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883379593 5000000000 14280988015369 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4734826743/10000000000 : ℝ)^4637 ≤ (19153514016341/50000000000000 : ℝ)^3613 := by
    have hnat : (4734826743 : ℕ)^4637*50000000000000^3613 ≤ 19153514016341^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4734826743 10000000000 19153514016341 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845692097/2000000000 : ℝ), (1883379593/5000000000 : ℝ), (4734826743/10000000000 : ℝ)] ![(16565497959627/50000000000000 : ℝ), (14280988015369/50000000000000 : ℝ), (19153514016341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845692097/2000000000 : ℝ)|^4637 ≤ (16565497959627/50000000000000 : ℝ)^3613
        have hw : |(845692097/2000000000 : ℝ)|=(845692097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1883379593/5000000000 : ℝ)|^4637 ≤ (14280988015369/50000000000000 : ℝ)^3613
        have hw : |(1883379593/5000000000 : ℝ)|=(1883379593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4734826743/10000000000 : ℝ)|^4637 ≤ (19153514016341/50000000000000 : ℝ)^3613
        have hw : |(4734826743/10000000000 : ℝ)|=(4734826743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s1_4 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-882413611/5000000000 : ℝ)*x 0 + (2564480073/5000000000 : ℝ)*x 1 + (5530535991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882413611/5000000000 : ℝ)^4637 ≤ (269862040871/2500000000000 : ℝ)^3613 := by
    have hnat : (882413611 : ℕ)^4637*2500000000000^3613 ≤ 269862040871^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882413611 5000000000 269862040871 2500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564480073/5000000000 : ℝ)^4637 ≤ (4244685829593/10000000000000 : ℝ)^3613 := by
    have hnat : (2564480073 : ℕ)^4637*10000000000000^3613 ≤ 4244685829593^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564480073 5000000000 4244685829593 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5530535991/10000000000 : ℝ)^4637 ≤ (46758660049809/100000000000000 : ℝ)^3613 := by
    have hnat : (5530535991 : ℕ)^4637*100000000000000^3613 ≤ 46758660049809^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530535991 10000000000 46758660049809 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882413611/5000000000 : ℝ), (2564480073/5000000000 : ℝ), (5530535991/10000000000 : ℝ)] ![(269862040871/2500000000000 : ℝ), (4244685829593/10000000000000 : ℝ), (46758660049809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882413611/5000000000 : ℝ)|^4637 ≤ (269862040871/2500000000000 : ℝ)^3613
        have hw : |(-882413611/5000000000 : ℝ)|=(882413611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564480073/5000000000 : ℝ)|^4637 ≤ (4244685829593/10000000000000 : ℝ)^3613
        have hw : |(2564480073/5000000000 : ℝ)|=(2564480073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5530535991/10000000000 : ℝ)|^4637 ≤ (46758660049809/100000000000000 : ℝ)^3613
        have hw : |(5530535991/10000000000 : ℝ)|=(5530535991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s1_5 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267732151/10000000000 : ℝ)*x 0 + (-1573319567/10000000000 : ℝ)*x 1 + (110610729/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267732151/10000000000 : ℝ)^4637 ≤ (21963219422667/50000000000000 : ℝ)^3613 := by
    have hnat : (5267732151 : ℕ)^4637*50000000000000^3613 ≤ 21963219422667^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267732151 10000000000 21963219422667 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1573319567/10000000000 : ℝ)^4637 ≤ (931489610301/10000000000000 : ℝ)^3613 := by
    have hnat : (1573319567 : ℕ)^4637*10000000000000^3613 ≤ 931489610301^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573319567 10000000000 931489610301 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110610729/200000000 : ℝ)^4637 ≤ (2922416564397/6250000000000 : ℝ)^3613 := by
    have hnat : (110610729 : ℕ)^4637*6250000000000^3613 ≤ 2922416564397^3613*200000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110610729 200000000 2922416564397 6250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267732151/10000000000 : ℝ), (-1573319567/10000000000 : ℝ), (110610729/200000000 : ℝ)] ![(21963219422667/50000000000000 : ℝ), (931489610301/10000000000000 : ℝ), (2922416564397/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267732151/10000000000 : ℝ)|^4637 ≤ (21963219422667/50000000000000 : ℝ)^3613
        have hw : |(5267732151/10000000000 : ℝ)|=(5267732151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1573319567/10000000000 : ℝ)|^4637 ≤ (931489610301/10000000000000 : ℝ)^3613
        have hw : |(-1573319567/10000000000 : ℝ)|=(1573319567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110610729/200000000 : ℝ)|^4637 ≤ (2922416564397/6250000000000 : ℝ)^3613
        have hw : |(110610729/200000000 : ℝ)|=(110610729/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s1_6 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329233227/625000000 : ℝ)*x 0 + (2765268321/5000000000 : ℝ)*x 1 + (-62932801/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329233227/625000000 : ℝ)^4637 ≤ (43926433290913/100000000000000 : ℝ)^3613 := by
    have hnat : (329233227 : ℕ)^4637*100000000000000^3613 ≤ 43926433290913^3613*625000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329233227 625000000 43926433290913 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2765268321/5000000000 : ℝ)^4637 ≤ (11689666778429/25000000000000 : ℝ)^3613 := by
    have hnat : (2765268321 : ℕ)^4637*25000000000000^3613 ≤ 11689666778429^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765268321 5000000000 11689666778429 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62932801/400000000 : ℝ)^4637 ≤ (4657449791571/50000000000000 : ℝ)^3613 := by
    have hnat : (62932801 : ℕ)^4637*50000000000000^3613 ≤ 4657449791571^3613*400000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62932801 400000000 4657449791571 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329233227/625000000 : ℝ), (2765268321/5000000000 : ℝ), (-62932801/400000000 : ℝ)] ![(43926433290913/100000000000000 : ℝ), (11689666778429/25000000000000 : ℝ), (4657449791571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329233227/625000000 : ℝ)|^4637 ≤ (43926433290913/100000000000000 : ℝ)^3613
        have hw : |(329233227/625000000 : ℝ)|=(329233227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2765268321/5000000000 : ℝ)|^4637 ≤ (11689666778429/25000000000000 : ℝ)^3613
        have hw : |(2765268321/5000000000 : ℝ)|=(2765268321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62932801/400000000 : ℝ)|^4637 ≤ (4657449791571/50000000000000 : ℝ)^3613
        have hw : |(-62932801/400000000 : ℝ)|=(62932801/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s1_7 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114478973/5000000000 : ℝ)*x 0 + (944967999/2000000000 : ℝ)*x 1 + (3776893701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114478973/5000000000 : ℝ)^4637 ≤ (16567999212681/50000000000000 : ℝ)^3613 := by
    have hnat : (2114478973 : ℕ)^4637*50000000000000^3613 ≤ 16567999212681^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114478973 5000000000 16567999212681 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (944967999/2000000000 : ℝ)^4637 ≤ (19101680854329/50000000000000 : ℝ)^3613 := by
    have hnat : (944967999 : ℕ)^4637*50000000000000^3613 ≤ 19101680854329^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944967999 2000000000 19101680854329 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3776893701/10000000000 : ℝ)^4637 ≤ (7165159963799/25000000000000 : ℝ)^3613 := by
    have hnat : (3776893701 : ℕ)^4637*25000000000000^3613 ≤ 7165159963799^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3776893701 10000000000 7165159963799 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114478973/5000000000 : ℝ), (944967999/2000000000 : ℝ), (3776893701/10000000000 : ℝ)] ![(16567999212681/50000000000000 : ℝ), (19101680854329/50000000000000 : ℝ), (7165159963799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114478973/5000000000 : ℝ)|^4637 ≤ (16567999212681/50000000000000 : ℝ)^3613
        have hw : |(2114478973/5000000000 : ℝ)|=(2114478973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(944967999/2000000000 : ℝ)|^4637 ≤ (19101680854329/50000000000000 : ℝ)^3613
        have hw : |(944967999/2000000000 : ℝ)|=(944967999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3776893701/10000000000 : ℝ)|^4637 ≤ (7165159963799/25000000000000 : ℝ)^3613
        have hw : |(3776893701/10000000000 : ℝ)|=(3776893701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1570_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9069/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3551/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (443/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (443/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (443/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (443/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (443/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (443/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (443/12500 : ℝ) ^ (4635/1024 : ℝ) ≤ (3399272268229/12500000000000000000 : ℝ) := by
    have hpowers : (443/12500 : ℝ)^4635 ≤ (3399272268229/12500000000000000000 : ℝ)^1024 := by
      have hnat : (443 : ℕ)^4635*12500000000000000000^1024 ≤ 3399272268229^1024*12500^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        443 12500 3399272268229 12500000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (443/12500 : ℝ)) (X := (3399272268229/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12377/50000 : ℝ) ^ (4635/1024 : ℝ) ≤ (7202385540860283/4000000000000000000 : ℝ) := by
    have hpowers : (12377/50000 : ℝ)^4635 ≤ (7202385540860283/4000000000000000000 : ℝ)^1024 := by
      have hnat : (12377 : ℕ)^4635*4000000000000000000^1024 ≤ 7202385540860283^1024*50000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12377 50000 7202385540860283 4000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12377/50000 : ℝ)) (X := (7202385540860283/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250003399272268229/6250000000000000000 : ℝ) ≤ (5000000600794661/5000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (6250003399272268229/6250000000000000000 : ℝ)^1024 ≤ (5000000600794661/5000000000000000 : ℝ)^4635 := by
      have hnat : (6250003399272268229 : ℕ)^1024*5000000000000000^4635 ≤ 5000000600794661^4635*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250003399272268229 6250000000000000000 5000000600794661 5000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000600794661/5000000000000000 : ℝ)) (X := (6250003399272268229/6250000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100180086832699652907/100000000000000000000 : ℝ) ≤ (2000795165873589/2000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (100180086832699652907/100000000000000000000 : ℝ)^1024 ≤ (2000795165873589/2000000000000000 : ℝ)^4635 := by
      have hnat : (100180086832699652907 : ℕ)^1024*2000000000000000^4635 ≤ 2000795165873589^4635*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100180086832699652907 100000000000000000000 2000795165873589 2000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000795165873589/2000000000000000 : ℝ)) (X := (100180086832699652907/100000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2007202385540860283/2000000000000000000 : ℝ) ≤ (1250993807143321/1250000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (2007202385540860283/2000000000000000000 : ℝ)^1024 ≤ (1250993807143321/1250000000000000 : ℝ)^4635 := by
      have hnat : (2007202385540860283 : ℕ)^1024*1250000000000000^4635 ≤ 1250993807143321^4635*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2007202385540860283 2000000000000000000 1250993807143321 1250000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250993807143321/1250000000000000 : ℝ)) (X := (2007202385540860283/2000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3399272268229/12500000000000000000 : ℝ) ≤ ((53017963331003659949/53025000000000000000 : ℝ)+2*(3974627778623/2121000000000000 : ℝ)*(443/12500 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (53017963331003659949/53025000000000000000 : ℝ)+2*(3974627778623/2121000000000000 : ℝ)*(443/12500 : ℝ)=(5000000600794661/5000000000000000 : ℝ) by norm_num, show 1+2*(3399272268229/12500000000000000000 : ℝ)=(6250003399272268229/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7202385540860283/4000000000000000000 : ℝ)+(3399272268229/12500000000000000000 : ℝ) ≤ ((53017963331003659949/53025000000000000000 : ℝ)+(3974627778623/2121000000000000 : ℝ)*((12377/50000 : ℝ)+(443/12500 : ℝ)))^(4635/1024 : ℝ) := by
    rw [show (53017963331003659949/53025000000000000000 : ℝ)+(3974627778623/2121000000000000 : ℝ)*((12377/50000 : ℝ)+(443/12500 : ℝ))=(2000795165873589/2000000000000000 : ℝ) by norm_num, show 1+(7202385540860283/4000000000000000000 : ℝ)+(3399272268229/12500000000000000000 : ℝ)=(100180086832699652907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7202385540860283/4000000000000000000 : ℝ) ≤ ((53017963331003659949/53025000000000000000 : ℝ)+2*(3974627778623/2121000000000000 : ℝ)*(12377/50000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (53017963331003659949/53025000000000000000 : ℝ)+2*(3974627778623/2121000000000000 : ℝ)*(12377/50000 : ℝ)=(1250993807143321/1250000000000000 : ℝ) by norm_num, show 1+2*(7202385540860283/4000000000000000000 : ℝ)=(2007202385540860283/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53017963331003659949/53025000000000000000 : ℝ)*(X 1 0+X 2 0)+(3974627778623/2121000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (443/12500 : ℝ)) (hi := (12377/50000 : ℝ)) (c := (53017963331003659949/53025000000000000000 : ℝ)) (alpha := (3974627778623/2121000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53017963331003659949/53025000000000000000 : ℝ)*(X 0 1+X 2 1)+(3974627778623/2121000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (443/12500 : ℝ)) (hi := (12377/50000 : ℝ)) (c := (53017963331003659949/53025000000000000000 : ℝ)) (alpha := (3974627778623/2121000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53017963331003659949/53025000000000000000 : ℝ)*(X 0 2+X 1 2)+(3974627778623/2121000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (443/12500 : ℝ)) (hi := (12377/50000 : ℝ)) (c := (53017963331003659949/53025000000000000000 : ℝ)) (alpha := (3974627778623/2121000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-220577/1250000 : ℝ)*X 0 0+(2767414591/5000000000 : ℝ)*X 0 1+(5124729373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376436917/10000000000 : ℝ)*X 1 0+(-494781619/2500000000 : ℝ)*X 1 1+(5124729121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376436823/10000000000 : ℝ)*X 2 0+(1281182367/2500000000 : ℝ)*X 2 1+(-989563073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((845692097/2000000000 : ℝ)*X 0 0+(1883379593/5000000000 : ℝ)*X 0 1+(4734826743/10000000000 : ℝ)*X 0 2+(845692097/2000000000 : ℝ)*X 1 0+(1883379593/5000000000 : ℝ)*X 1 1+(4734826743/10000000000 : ℝ)*X 1 2+(845692097/2000000000 : ℝ)*X 2 0+(1883379593/5000000000 : ℝ)*X 2 1+(4734826743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-882413611/5000000000 : ℝ)*X 0 0+(2564480073/5000000000 : ℝ)*X 0 1+(5530535991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5267732151/10000000000 : ℝ)*X 1 0+(-1573319567/10000000000 : ℝ)*X 1 1+(110610729/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329233227/625000000 : ℝ)*X 2 0+(2765268321/5000000000 : ℝ)*X 2 1+(-62932801/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2114478973/5000000000 : ℝ)*X 0 0+(944967999/2000000000 : ℝ)*X 0 1+(3776893701/10000000000 : ℝ)*X 0 2+(2114478973/5000000000 : ℝ)*X 1 0+(944967999/2000000000 : ℝ)*X 1 1+(3776893701/10000000000 : ℝ)*X 1 2+(2114478973/5000000000 : ℝ)*X 2 0+(944967999/2000000000 : ℝ)*X 2 1+(3776893701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95950347160828979942236023/11046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1976021/2000000000000 : ℝ)*(base1) + (2107930733/100000000000000 : ℝ)*(base19) + (2065297369/100000000000000 : ℝ)*(base23) + (27211981/20000000000000 : ℝ)*(upper3) + (316616209/100000000000000 : ℝ)*(upper5) + (21696678283877/1250000000000 : ℝ)*(major0) + (21696678283877/1250000000000 : ℝ)*(major1) + (21696678283877/1250000000000 : ℝ)*(major2) + (487689350168023/20000000000000 : ℝ)*(sp0) + (1219231876767199/50000000000000 : ℝ)*(sp1) + (1219231898083881/50000000000000 : ℝ)*(sp2) + (103299449692921/10000000000000 : ℝ)*(sp3) + (3841885213/20000000000000 : ℝ)*(sp4) + (7778700063/100000000000000 : ℝ)*(sp7) + (41320094977213/4000000000000 : ℝ)*(f.failure) + (243846586146513/10000000000000 : ℝ)*(f.sum) + (106197160039/5302500000000000000000000000 : ℝ)*base65 + (193565724129788977/66281250000000000000000000000000 : ℝ)*base68 + (150236091435898523/66281250000000000000000000000000 : ℝ)*base69 + (260370877633820227/66281250000000000000000000000000 : ℝ)*base72 + (13038397063717/10605000000000000000000000000 : ℝ)*base74 + (340417546020601477/66281250000000000000000000000000 : ℝ)*base76 + (53422511479929773/66281250000000000000000000000000 : ℝ)*base77 + (787191813652163977/66281250000000000000000000000000 : ℝ)*base80 + (20994688488337/10605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (36853/4000000000000000000 : ℝ)*base89 + (36853/4000000000000000000 : ℝ)*base91 + (36853/4000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99506028200017402174210801/13808593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (634968553/50000000000000 : ℝ)*(base19) + (1140840167/100000000000000 : ℝ)*(base23) + (34863127/50000000000000 : ℝ)*(upper2) + (126579679/50000000000000 : ℝ)*(upper3) + (30692233/25000000000000 : ℝ)*(upper5) + (6924020398297/390625000000 : ℝ)*(major0) + (6924020398297/390625000000 : ℝ)*(major1) + (6924020398297/390625000000 : ℝ)*(major2) + (10564962777/100000000000000 : ℝ)*(sp1) + (9783865983/100000000000000 : ℝ)*(sp2) + (2490185827780631/100000000000000 : ℝ)*(sp4) + (622543498220187/25000000000000 : ℝ)*(sp5) + (31127186288431/1250000000000 : ℝ)*(sp6) + (26372809398607/2500000000000 : ℝ)*(sp7) + (26372809398607/2500000000000 : ℝ)*(f.failure) + (2490185827780631/100000000000000 : ℝ)*(f.sum) + (32133697922491/26512500000000000000000000000 : ℝ)*base66 + (380623737619068037/82851562500000000000000000000000 : ℝ)*base67 + (243569625923973301/165703125000000000000000000000000 : ℝ)*base70 + (366707404852901699/165703125000000000000000000000000 : ℝ)*base71 + (7159750339729/6628125000000000000000000000 : ℝ)*base74 + (503419515418526699/165703125000000000000000000000000 : ℝ)*base75 + (1641946075997276699/165703125000000000000000000000000 : ℝ)*base77 + (268679045832229331/41425781250000000000000000000000 : ℝ)*base79 + (163824333405541/26512500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (31433/2500000000000000000 : ℝ)*base90 + (31433/2500000000000000000 : ℝ)*base92 + (31433/2500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1570_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9069/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3551/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1570_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1570_s2_0 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-891605599/5000000000 : ℝ)*x 0 + (5441449757/10000000000 : ℝ)*x 1 + (5205991267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891605599/5000000000 : ℝ)^4637 ≤ (5469504022369/50000000000000 : ℝ)^3613 := by
    have hnat : (891605599 : ℕ)^4637*50000000000000^3613 ≤ 5469504022369^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891605599 5000000000 5469504022369 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441449757/10000000000 : ℝ)^4637 ≤ (45794213353639/100000000000000 : ℝ)^3613 := by
    have hnat : (5441449757 : ℕ)^4637*100000000000000^3613 ≤ 45794213353639^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441449757 10000000000 45794213353639 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205991267/10000000000 : ℝ)^4637 ≤ (10816694645291/25000000000000 : ℝ)^3613 := by
    have hnat : (5205991267 : ℕ)^4637*25000000000000^3613 ≤ 10816694645291^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205991267 10000000000 10816694645291 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-891605599/5000000000 : ℝ), (5441449757/10000000000 : ℝ), (5205991267/10000000000 : ℝ)] ![(5469504022369/50000000000000 : ℝ), (45794213353639/100000000000000 : ℝ), (10816694645291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-891605599/5000000000 : ℝ)|^4637 ≤ (5469504022369/50000000000000 : ℝ)^3613
        have hw : |(-891605599/5000000000 : ℝ)|=(891605599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441449757/10000000000 : ℝ)|^4637 ≤ (45794213353639/100000000000000 : ℝ)^3613
        have hw : |(5441449757/10000000000 : ℝ)|=(5441449757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205991267/10000000000 : ℝ)|^4637 ≤ (10816694645291/25000000000000 : ℝ)^3613
        have hw : |(5205991267/10000000000 : ℝ)|=(5205991267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s2_1 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20907497/39062500 : ℝ)*x 0 + (-238007773/1250000000 : ℝ)*x 1 + (1041198163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20907497/39062500 : ℝ)^4637 ≤ (44833755442503/100000000000000 : ℝ)^3613 := by
    have hnat : (20907497 : ℕ)^4637*100000000000000^3613 ≤ 44833755442503^3613*39062500^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20907497 39062500 44833755442503 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238007773/1250000000 : ℝ)^4637 ≤ (594973539387/5000000000000 : ℝ)^3613 := by
    have hnat : (238007773 : ℕ)^4637*5000000000000^3613 ≤ 594973539387^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238007773 1250000000 594973539387 5000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041198163/2000000000 : ℝ)^4637 ≤ (1730670950397/4000000000000 : ℝ)^3613 := by
    have hnat : (1041198163 : ℕ)^4637*4000000000000^3613 ≤ 1730670950397^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041198163 2000000000 1730670950397 4000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20907497/39062500 : ℝ), (-238007773/1250000000 : ℝ), (1041198163/2000000000 : ℝ)] ![(44833755442503/100000000000000 : ℝ), (594973539387/5000000000000 : ℝ), (1730670950397/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20907497/39062500 : ℝ)|^4637 ≤ (44833755442503/100000000000000 : ℝ)^3613
        have hw : |(20907497/39062500 : ℝ)|=(20907497/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238007773/1250000000 : ℝ)|^4637 ≤ (594973539387/5000000000000 : ℝ)^3613
        have hw : |(-238007773/1250000000 : ℝ)|=(238007773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041198163/2000000000 : ℝ)|^4637 ≤ (1730670950397/4000000000000 : ℝ)^3613
        have hw : |(1041198163/2000000000 : ℝ)|=(1041198163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s2_2 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6690399/12500000 : ℝ)*x 0 + (5205990753/10000000000 : ℝ)*x 1 + (-1904062309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6690399/12500000 : ℝ)^4637 ≤ (11208438774621/25000000000000 : ℝ)^3613 := by
    have hnat : (6690399 : ℕ)^4637*25000000000000^3613 ≤ 11208438774621^3613*12500000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6690399 12500000 11208438774621 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205990753/10000000000 : ℝ)^4637 ≤ (10816693274651/25000000000000 : ℝ)^3613 := by
    have hnat : (5205990753 : ℕ)^4637*25000000000000^3613 ≤ 10816693274651^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205990753 10000000000 10816693274651 25000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904062309/10000000000 : ℝ)^4637 ≤ (2379894358067/20000000000000 : ℝ)^3613 := by
    have hnat : (1904062309 : ℕ)^4637*20000000000000^3613 ≤ 2379894358067^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904062309 10000000000 2379894358067 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6690399/12500000 : ℝ), (5205990753/10000000000 : ℝ), (-1904062309/10000000000 : ℝ)] ![(11208438774621/25000000000000 : ℝ), (10816693274651/25000000000000 : ℝ), (2379894358067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6690399/12500000 : ℝ)|^4637 ≤ (11208438774621/25000000000000 : ℝ)^3613
        have hw : |(6690399/12500000 : ℝ)|=(6690399/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205990753/10000000000 : ℝ)|^4637 ≤ (10816693274651/25000000000000 : ℝ)^3613
        have hw : |(5205990753/10000000000 : ℝ)|=(5205990753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904062309/10000000000 : ℝ)|^4637 ≤ (2379894358067/20000000000000 : ℝ)^3613
        have hw : |(-1904062309/10000000000 : ℝ)|=(1904062309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s2_3 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120969007/5000000000 : ℝ)*x 0 + (3971397497/10000000000 : ℝ)*x 1 + (2263606879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120969007/5000000000 : ℝ)^4637 ≤ (6653317179573/20000000000000 : ℝ)^3613 := by
    have hnat : (2120969007 : ℕ)^4637*20000000000000^3613 ≤ 6653317179573^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120969007 5000000000 6653317179573 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3971397497/10000000000 : ℝ)^4637 ≤ (30568595929333/100000000000000 : ℝ)^3613 := by
    have hnat : (3971397497 : ℕ)^4637*100000000000000^3613 ≤ 30568595929333^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3971397497 10000000000 30568595929333 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263606879/5000000000 : ℝ)^4637 ≤ (36164818158031/100000000000000 : ℝ)^3613 := by
    have hnat : (2263606879 : ℕ)^4637*100000000000000^3613 ≤ 36164818158031^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263606879 5000000000 36164818158031 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120969007/5000000000 : ℝ), (3971397497/10000000000 : ℝ), (2263606879/5000000000 : ℝ)] ![(6653317179573/20000000000000 : ℝ), (30568595929333/100000000000000 : ℝ), (36164818158031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120969007/5000000000 : ℝ)|^4637 ≤ (6653317179573/20000000000000 : ℝ)^3613
        have hw : |(2120969007/5000000000 : ℝ)|=(2120969007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3971397497/10000000000 : ℝ)|^4637 ≤ (30568595929333/100000000000000 : ℝ)^3613
        have hw : |(3971397497/10000000000 : ℝ)|=(3971397497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263606879/5000000000 : ℝ)|^4637 ≤ (36164818158031/100000000000000 : ℝ)^3613
        have hw : |(2263606879/5000000000 : ℝ)|=(2263606879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s2_4 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-891625419/5000000000 : ℝ)*x 0 + (2603696857/5000000000 : ℝ)*x 1 + (680004473/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891625419/5000000000 : ℝ)^4637 ≤ (2187864026869/20000000000000 : ℝ)^3613 := by
    have hnat : (891625419 : ℕ)^4637*20000000000000^3613 ≤ 2187864026869^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891625419 5000000000 2187864026869 20000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603696857/5000000000 : ℝ)^4637 ≤ (2705108643459/6250000000000 : ℝ)^3613 := by
    have hnat : (2603696857 : ℕ)^4637*6250000000000^3613 ≤ 2705108643459^3613*5000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603696857 5000000000 2705108643459 6250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680004473/1250000000 : ℝ)^4637 ≤ (1144473538833/2500000000000 : ℝ)^3613 := by
    have hnat : (680004473 : ℕ)^4637*2500000000000^3613 ≤ 1144473538833^3613*1250000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680004473 1250000000 1144473538833 2500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-891625419/5000000000 : ℝ), (2603696857/5000000000 : ℝ), (680004473/1250000000 : ℝ)] ![(2187864026869/20000000000000 : ℝ), (2705108643459/6250000000000 : ℝ), (1144473538833/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-891625419/5000000000 : ℝ)|^4637 ≤ (2187864026869/20000000000000 : ℝ)^3613
        have hw : |(-891625419/5000000000 : ℝ)|=(891625419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603696857/5000000000 : ℝ)|^4637 ≤ (2705108643459/6250000000000 : ℝ)^3613
        have hw : |(2603696857/5000000000 : ℝ)|=(2603696857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680004473/1250000000 : ℝ)|^4637 ≤ (1144473538833/2500000000000 : ℝ)^3613
        have hw : |(680004473/1250000000 : ℝ)|=(680004473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s2_5 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290017253/10000000000 : ℝ)*x 0 + (-52188051/312500000 : ℝ)*x 1 + (5440036681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290017253/10000000000 : ℝ)^4637 ≤ (44165080413217/100000000000000 : ℝ)^3613 := by
    have hnat : (5290017253 : ℕ)^4637*100000000000000^3613 ≤ 44165080413217^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290017253 10000000000 44165080413217 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52188051/312500000 : ℝ)^4637 ≤ (5027984162207/50000000000000 : ℝ)^3613 := by
    have hnat : (52188051 : ℕ)^4637*50000000000000^3613 ≤ 5027984162207^3613*312500000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52188051 312500000 5027984162207 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440036681/10000000000 : ℝ)^4637 ≤ (45778951241129/100000000000000 : ℝ)^3613 := by
    have hnat : (5440036681 : ℕ)^4637*100000000000000^3613 ≤ 45778951241129^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440036681 10000000000 45778951241129 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290017253/10000000000 : ℝ), (-52188051/312500000 : ℝ), (5440036681/10000000000 : ℝ)] ![(44165080413217/100000000000000 : ℝ), (5027984162207/50000000000000 : ℝ), (45778951241129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290017253/10000000000 : ℝ)|^4637 ≤ (44165080413217/100000000000000 : ℝ)^3613
        have hw : |(5290017253/10000000000 : ℝ)|=(5290017253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52188051/312500000 : ℝ)|^4637 ≤ (5027984162207/50000000000000 : ℝ)^3613
        have hw : |(-52188051/312500000 : ℝ)|=(52188051/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440036681/10000000000 : ℝ)|^4637 ≤ (45778951241129/100000000000000 : ℝ)^3613
        have hw : |(5440036681/10000000000 : ℝ)|=(5440036681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s2_6 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290017581/10000000000 : ℝ)*x 0 + (340002359/625000000 : ℝ)*x 1 + (-417503923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290017581/10000000000 : ℝ)^4637 ≤ (2760317745483/6250000000000 : ℝ)^3613 := by
    have hnat : (5290017581 : ℕ)^4637*6250000000000^3613 ≤ 2760317745483^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290017581 10000000000 2760317745483 6250000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340002359/625000000 : ℝ)^4637 ≤ (22889481360889/50000000000000 : ℝ)^3613 := by
    have hnat : (340002359 : ℕ)^4637*50000000000000^3613 ≤ 22889481360889^3613*625000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340002359 625000000 22889481360889 50000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417503923/2500000000 : ℝ)^4637 ≤ (1256994166491/12500000000000 : ℝ)^3613 := by
    have hnat : (417503923 : ℕ)^4637*12500000000000^3613 ≤ 1256994166491^3613*2500000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417503923 2500000000 1256994166491 12500000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290017581/10000000000 : ℝ), (340002359/625000000 : ℝ), (-417503923/2500000000 : ℝ)] ![(2760317745483/6250000000000 : ℝ), (22889481360889/50000000000000 : ℝ), (1256994166491/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290017581/10000000000 : ℝ)|^4637 ≤ (2760317745483/6250000000000 : ℝ)^3613
        have hw : |(5290017581/10000000000 : ℝ)|=(5290017581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340002359/625000000 : ℝ)|^4637 ≤ (22889481360889/50000000000000 : ℝ)^3613
        have hw : |(340002359/625000000 : ℝ)|=(340002359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417503923/2500000000 : ℝ)|^4637 ≤ (1256994166491/12500000000000 : ℝ)^3613
        have hw : |(-417503923/2500000000 : ℝ)|=(417503923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1570_s2_7 (p : ℝ) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242032191/10000000000 : ℝ)*x 0 + (904780667/2000000000 : ℝ)*x 1 + (3974736423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242032191/10000000000 : ℝ)^4637 ≤ (33267533790757/100000000000000 : ℝ)^3613 := by
    have hnat : (4242032191 : ℕ)^4637*100000000000000^3613 ≤ 33267533790757^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242032191 10000000000 33267533790757 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904780667/2000000000 : ℝ)^4637 ≤ (36130881982531/100000000000000 : ℝ)^3613 := by
    have hnat : (904780667 : ℕ)^4637*100000000000000^3613 ≤ 36130881982531^3613*2000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904780667 2000000000 36130881982531 100000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3974736423/10000000000 : ℝ)^4637 ≤ (3060158421837/10000000000000 : ℝ)^3613 := by
    have hnat : (3974736423 : ℕ)^4637*10000000000000^3613 ≤ 3060158421837^3613*10000000000^4637 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3974736423 10000000000 3060158421837 10000000000000 4637 3613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4637/1024 : ℝ)) 4637 3613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242032191/10000000000 : ℝ), (904780667/2000000000 : ℝ), (3974736423/10000000000 : ℝ)] ![(33267533790757/100000000000000 : ℝ), (36130881982531/100000000000000 : ℝ), (3060158421837/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242032191/10000000000 : ℝ)|^4637 ≤ (33267533790757/100000000000000 : ℝ)^3613
        have hw : |(4242032191/10000000000 : ℝ)|=(4242032191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904780667/2000000000 : ℝ)|^4637 ≤ (36130881982531/100000000000000 : ℝ)^3613
        have hw : |(904780667/2000000000 : ℝ)|=(904780667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3974736423/10000000000 : ℝ)|^4637 ≤ (3060158421837/10000000000000 : ℝ)^3613
        have hw : |(3974736423/10000000000 : ℝ)|=(3974736423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1570_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3551/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (541/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3953/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3551/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3551/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3551/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3551/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3551/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3551/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (9069/100000 : ℝ) ^ (4635/1024 : ℝ) ≤ (1912190172405401/100000000000000000000 : ℝ) := by
    have hpowers : (9069/100000 : ℝ)^4635 ≤ (1912190172405401/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9069 : ℕ)^4635*100000000000000000000^1024 ≤ 1912190172405401^1024*100000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9069 100000 1912190172405401 100000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9069/100000 : ℝ)) (X := (1912190172405401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3551/20000 : ℝ) ^ (4635/1024 : ℝ) ≤ (10002066808312261/25000000000000000000 : ℝ) := by
    have hpowers : (3551/20000 : ℝ)^4635 ≤ (10002066808312261/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3551 : ℕ)^4635*25000000000000000000^1024 ≤ 10002066808312261^1024*20000^4635 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3551 20000 10002066808312261 25000000000000000000 4635 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3551/20000 : ℝ)) (X := (10002066808312261/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001912190172405401/50000000000000000000 : ℝ) ≤ (10000084489905803/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (50001912190172405401/50000000000000000000 : ℝ)^1024 ≤ (10000084489905803/10000000000000000 : ℝ)^4635 := by
      have hnat : (50001912190172405401 : ℕ)^1024*10000000000000000^4635 ≤ 10000084489905803^4635*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001912190172405401 50000000000000000000 10000084489905803 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084489905803/10000000000000000 : ℝ)) (X := (50001912190172405401/50000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008384091481130889/20000000000000000000 : ℝ) ≤ (10000925987927089/10000000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (20008384091481130889/20000000000000000000 : ℝ)^1024 ≤ (10000925987927089/10000000000000000 : ℝ)^4635 := by
      have hnat : (20008384091481130889 : ℕ)^1024*10000000000000000^4635 ≤ 10000925987927089^4635*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008384091481130889 20000000000000000000 10000925987927089 10000000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000925987927089/10000000000000000 : ℝ)) (X := (20008384091481130889/20000000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12510002066808312261/12500000000000000000 : ℝ) ≤ (80014139887587/80000000000000 : ℝ) ^ (4635/1024 : ℝ) := by
    have hpowers : (12510002066808312261/12500000000000000000 : ℝ)^1024 ≤ (80014139887587/80000000000000 : ℝ)^4635 := by
      have hnat : (12510002066808312261 : ℕ)^1024*80000000000000^4635 ≤ 80014139887587^4635*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510002066808312261 12500000000000000000 80014139887587 80000000000000 1024 4635 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80014139887587/80000000000000 : ℝ)) (X := (12510002066808312261/12500000000000000000 : ℝ)) (by norm_num) 4635 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1912190172405401/100000000000000000000 : ℝ) ≤ ((8684547078821171939/8686000000000000000 : ℝ)+2*(420749010643/434300000000000 : ℝ)*(9069/100000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (8684547078821171939/8686000000000000000 : ℝ)+2*(420749010643/434300000000000 : ℝ)*(9069/100000 : ℝ)=(10000084489905803/10000000000000000 : ℝ) by norm_num, show 1+2*(1912190172405401/100000000000000000000 : ℝ)=(50001912190172405401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10002066808312261/25000000000000000000 : ℝ)+(1912190172405401/100000000000000000000 : ℝ) ≤ ((8684547078821171939/8686000000000000000 : ℝ)+(420749010643/434300000000000 : ℝ)*((3551/20000 : ℝ)+(9069/100000 : ℝ)))^(4635/1024 : ℝ) := by
    rw [show (8684547078821171939/8686000000000000000 : ℝ)+(420749010643/434300000000000 : ℝ)*((3551/20000 : ℝ)+(9069/100000 : ℝ))=(10000925987927089/10000000000000000 : ℝ) by norm_num, show 1+(10002066808312261/25000000000000000000 : ℝ)+(1912190172405401/100000000000000000000 : ℝ)=(20008384091481130889/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10002066808312261/25000000000000000000 : ℝ) ≤ ((8684547078821171939/8686000000000000000 : ℝ)+2*(420749010643/434300000000000 : ℝ)*(3551/20000 : ℝ))^(4635/1024 : ℝ) := by
    rw [show (8684547078821171939/8686000000000000000 : ℝ)+2*(420749010643/434300000000000 : ℝ)*(3551/20000 : ℝ)=(80014139887587/80000000000000 : ℝ) by norm_num, show 1+2*(10002066808312261/25000000000000000000 : ℝ)=(12510002066808312261/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8684547078821171939/8686000000000000000 : ℝ)*(X 1 0+X 2 0)+(420749010643/434300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (9069/100000 : ℝ)) (hi := (3551/20000 : ℝ)) (c := (8684547078821171939/8686000000000000000 : ℝ)) (alpha := (420749010643/434300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8684547078821171939/8686000000000000000 : ℝ)*(X 0 1+X 2 1)+(420749010643/434300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (9069/100000 : ℝ)) (hi := (3551/20000 : ℝ)) (c := (8684547078821171939/8686000000000000000 : ℝ)) (alpha := (420749010643/434300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8684547078821171939/8686000000000000000 : ℝ)*(X 0 2+X 1 2)+(420749010643/434300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4635/1024 : ℝ)) (lo := (9069/100000 : ℝ)) (hi := (3551/20000 : ℝ)) (c := (8684547078821171939/8686000000000000000 : ℝ)) (alpha := (420749010643/434300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-891605599/5000000000 : ℝ)*X 0 0+(5441449757/10000000000 : ℝ)*X 0 1+(5205991267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20907497/39062500 : ℝ)*X 1 0+(-238007773/1250000000 : ℝ)*X 1 1+(1041198163/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((6690399/12500000 : ℝ)*X 2 0+(5205990753/10000000000 : ℝ)*X 2 1+(-1904062309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2120969007/5000000000 : ℝ)*X 0 0+(3971397497/10000000000 : ℝ)*X 0 1+(2263606879/5000000000 : ℝ)*X 0 2+(2120969007/5000000000 : ℝ)*X 1 0+(3971397497/10000000000 : ℝ)*X 1 1+(2263606879/5000000000 : ℝ)*X 1 2+(2120969007/5000000000 : ℝ)*X 2 0+(3971397497/10000000000 : ℝ)*X 2 1+(2263606879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-891625419/5000000000 : ℝ)*X 0 0+(2603696857/5000000000 : ℝ)*X 0 1+(680004473/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290017253/10000000000 : ℝ)*X 1 0+(-52188051/312500000 : ℝ)*X 1 1+(5440036681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290017581/10000000000 : ℝ)*X 2 0+(340002359/625000000 : ℝ)*X 2 1+(-417503923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242032191/10000000000 : ℝ)*X 0 0+(904780667/2000000000 : ℝ)*X 0 1+(3974736423/10000000000 : ℝ)*X 0 2+(4242032191/10000000000 : ℝ)*X 1 0+(904780667/2000000000 : ℝ)*X 1 1+(3974736423/10000000000 : ℝ)*X 1 2+(4242032191/10000000000 : ℝ)*X 2 0+(904780667/2000000000 : ℝ)*X 2 1+(3974736423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1570_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24018465915340940787701721/5428750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19457139/4000000000000 : ℝ)*(base19) + (308971497/50000000000000 : ℝ)*(base23) + (2576773/6250000000000 : ℝ)*(upper3) + (91369393/100000000000000 : ℝ)*(lower4) + (54593799/50000000000000 : ℝ)*(upper5) + (75577436836687/2500000000000 : ℝ)*(major0) + (75577436836687/2500000000000 : ℝ)*(major1) + (75577436836687/2500000000000 : ℝ)*(major2) + (212351647443511/5000000000000 : ℝ)*(sp0) + (849406492488349/20000000000000 : ℝ)*(sp1) + (4247031145063997/100000000000000 : ℝ)*(sp2) + (44978984494177/2500000000000 : ℝ)*(sp3) + (118586323/10000000000000 : ℝ)*(sp6) + (2470820697/100000000000000 : ℝ)*(sp7) + (1799161850587777/100000000000000 : ℝ)*(f.failure) + (212351647443511/5000000000000 : ℝ)*(f.sum) + (25918166521713/4343000000000000000000000000 : ℝ)*base66 + (257200380036521093/21715000000000000000000000000000 : ℝ)*base67 + (135187216973081093/21715000000000000000000000000000 : ℝ)*base69 + (181977094755741093/21715000000000000000000000000000 : ℝ)*base71 + (8327519881903/4343000000000000000000000000 : ℝ)*base73 + (46021009382056093/21715000000000000000000000000000 : ℝ)*base75 + (84903494905108907/21715000000000000000000000000000 : ℝ)*base78 + (75805510326006093/21715000000000000000000000000000 : ℝ)*base79 + (1144534433647/2171500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (525337/100000000000000000000 : ℝ)*base89 + (525337/100000000000000000000 : ℝ)*base91 + (525337/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (326703711843744272924553/21715000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112257591/12500000000000 : ℝ)*(base23) + (96001779/100000000000000 : ℝ)*(lower2) + (221544167/100000000000000 : ℝ)*(upper3) + (169307641/100000000000000 : ℝ)*(lower4) + (5056109/6250000000000 : ℝ)*(upper5) + (3059695326181639/100000000000000 : ℝ)*(major0) + (3059695326181639/100000000000000 : ℝ)*(major1) + (3059695326181639/100000000000000 : ℝ)*(major2) + (876038617/12500000000000 : ℝ)*(sp1) + (48866132067/100000000000000 : ℝ)*(sp2) + (4298447507230687/100000000000000 : ℝ)*(sp4) + (4298440498921751/100000000000000 : ℝ)*(sp5) + (1074599435759473/25000000000000 : ℝ)*(sp6) + (910471321815113/50000000000000 : ℝ)*(sp7) + (910471321815113/50000000000000 : ℝ)*(f.failure) + (4298447507230687/100000000000000 : ℝ)*(f.sum) + (247357652190023/21715000000000000000000000000 : ℝ)*base66 + (7664203458600568021/868600000000000000000000000000000 : ℝ)*base67 + (8017532585709768021/868600000000000000000000000000000 : ℝ)*base69 + (3300418454379231979/868600000000000000000000000000000 : ℝ)*base72 + (25484083655733/21715000000000000000000000000 : ℝ)*base74 + (550570306372031979/868600000000000000000000000000000 : ℝ)*base76 + (6834633487126568021/868600000000000000000000000000000 : ℝ)*base77 + (3062372968056031979/868600000000000000000000000000000 : ℝ)*base80 + (12743757971661/2714375000000000000000000000 : ℝ)*base82 + (386753/50000000000000000000 : ℝ)*base89 + (386753/50000000000000000000 : ℝ)*base91 + (386753/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1570_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3551/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1570_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1570_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1570_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1570_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1570_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4635/1024 : ℝ) ≤ p) (hpb : p ≤ (4637/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1680281/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1570_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
