-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff6.positive_w036_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T19:50:06.255013+00:00
-- url     : https://prove2.me/submissions/e469901d-1a0e-48eb-8d87-678d4c6f7289

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
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
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff6
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
theorem support_w036_box_0 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-510124053/10000000000 : ℝ)*x 0 + (5400002789/10000000000 : ℝ)*x 1 + (5400002851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-510124053/10000000000 : ℝ), (5400002789/10000000000 : ℝ), (5400002851/10000000000 : ℝ)] ![(3031765550639/100000000000000 : ℝ), (484841168847/1000000000000 : ℝ), (4848411753871/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_1 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5155045951/10000000000 : ℝ)*x 0 + (-860707711/10000000000 : ℝ)*x 1 + (1350000711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5155045951/10000000000 : ℝ), (-860707711/10000000000 : ℝ), (1350000711/2500000000 : ℝ)] ![(45910555541869/100000000000000 : ℝ), (1121065396003/20000000000000 : ℝ), (48484117464871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_2 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5155046113/10000000000 : ℝ)*x 0 + (1080000557/2000000000 : ℝ)*x 1 + (-860707571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5155046113/10000000000 : ℝ), (1080000557/2000000000 : ℝ), (-860707571/10000000000 : ℝ)] ![(45910557236919/100000000000000 : ℝ), (24242058421253/50000000000000 : ℝ), (5605325908839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_6 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (919947551/2000000000 : ℝ)*x 0 + (3580788751/10000000000 : ℝ)*x 1 + (3580789087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(919947551/2000000000 : ℝ), (3580788751/10000000000 : ℝ), (3580789087/10000000000 : ℝ)] ![(2509790387347/6250000000000 : ℝ), (5984335048609/20000000000000 : ℝ), (7480419635419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_7 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1404079997/10000000000 : ℝ)*x 0 + (1267440711/2500000000 : ℝ)*x 1 + (5069762801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1404079997/10000000000 : ℝ), (1267440711/2500000000 : ℝ), (5069762801/10000000000 : ℝ)] ![(4980488106061/50000000000000 : ℝ), (45019512110749/100000000000000 : ℝ), (45019511662139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_8 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5370576389/10000000000 : ℝ)*x 0 + (-50769773/500000000 : ℝ)*x 1 + (5069762817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5370576389/10000000000 : ℝ), (-50769773/500000000 : ℝ), (5069762817/10000000000 : ℝ)] ![(24086929533897/50000000000000 : ℝ), (136132581923/2000000000000 : ℝ), (5627438978633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_9 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (671322041/1250000000 : ℝ)*x 0 + (40558103/80000000 : ℝ)*x 1 + (-1015395463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(671322041/1250000000 : ℝ), (40558103/80000000 : ℝ), (-1015395463/10000000000 : ℝ)] ![(48173858424947/100000000000000 : ℝ), (22509756217083/50000000000000 : ℝ), (6806629119777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_13 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1529350589/5000000000 : ℝ)*x 0 + (1086524393/2500000000 : ℝ)*x 1 + (434609749/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1529350589/5000000000 : ℝ), (1086524393/2500000000 : ℝ), (434609749/1000000000 : ℝ)] ![(24864304514483/100000000000000 : ℝ), (37567848150733/100000000000000 : ℝ), (4695980914747/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_14 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-301443/2500000 : ℝ)*x 0 + (600643341/1250000000 : ℝ)*x 1 + (1714567/3125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-301443/2500000 : ℝ), (600643341/1250000000 : ℝ), (1714567/3125000 : ℝ)] ![(8329369223849/100000000000000 : ℝ), (21135805564617/50000000000000 : ℝ), (49399019623023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_15 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5098726147/10000000000 : ℝ)*x 0 + (-102235809/1250000000 : ℝ)*x 1 + (5486615681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5098726147/10000000000 : ℝ), (-102235809/1250000000 : ℝ), (5486615681/10000000000 : ℝ)] ![(11330457723477/25000000000000 : ℝ), (2639567958397/50000000000000 : ℝ), (4939903317337/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_16 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5098729297/10000000000 : ℝ)*x 0 + (5486612321/10000000000 : ℝ)*x 1 + (-40894341/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5098729297/10000000000 : ℝ), (5486612321/10000000000 : ℝ), (-40894341/500000000 : ℝ)] ![(9064372757991/20000000000000 : ℝ), (24699498815739/50000000000000 : ℝ), (41243269967/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_20 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (155666277/312500000 : ℝ)*x 0 + (675806909/2000000000 : ℝ)*x 1 + (1689516291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(155666277/312500000 : ℝ), (675806909/2000000000 : ℝ), (1689516291/5000000000 : ℝ)] ![(44098229557403/100000000000000 : ℝ), (13975447375597/50000000000000 : ℝ), (5590175134833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_21 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-169004171/2500000000 : ℝ)*x 0 + (2823103181/5000000000 : ℝ)*x 1 + (251898979/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-169004171/2500000000 : ℝ), (2823103181/5000000000 : ℝ), (251898979/500000000 : ℝ)] ![(33763681187/800000000000 : ℝ), (10218286763381/20000000000000 : ℝ), (22344053012019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_22 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1347865783/2500000000 : ℝ)*x 0 + (-1029500283/10000000000 : ℝ)*x 1 + (19679607/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1347865783/2500000000 : ℝ), (-1029500283/10000000000 : ℝ), (19679607/39062500 : ℝ)] ![(48394048323633/100000000000000 : ℝ), (6917847591289/100000000000000 : ℝ), (44688104064829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_23 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (539146307/1000000000 : ℝ)*x 0 + (629747453/1250000000 : ℝ)*x 1 + (-1029500061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(539146307/1000000000 : ℝ), (629747453/1250000000 : ℝ), (-1029500061/10000000000 : ℝ)] ![(48394047669803/100000000000000 : ℝ), (2793006655161/6250000000000 : ℝ), (6917845838681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w036_box_27 (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1451041051/5000000000 : ℝ)*x 0 + (4419299583/10000000000 : ℝ)*x 1 + (138103121/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (215/32 : ℝ)) 215 183 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1451041051/5000000000 : ℝ), (4419299583/10000000000 : ℝ), (138103121/312500000 : ℝ)] ![(23375305293017/100000000000000 : ℝ), (19156172939427/50000000000000 : ℝ), (19156174411199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_w036_box (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26043/10000 : ℝ) (148023/100000 : ℝ) (84849/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2283/12500 : ℝ)*pair X i i) :
    -(4519/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59201/100000 : ℝ) ∧ (82889/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (12007/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f (by norm_num)
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have ratio0 : (X 1 1+X 2 1) ≤ (2283/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have ratio1 : (X 1 2+X 2 2) ≤ (2283/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have ratio2 : (X 0 0+X 2 0) ≤ (2283/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have ratio3 : (X 0 2+X 2 2) ≤ (2283/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have ratio4 : (X 0 0+X 1 0) ≤ (2283/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have ratio5 : (X 0 1+X 1 1) ≤ (2283/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
  have base53 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign3]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
  have base61 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [sign5]
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
  have hpow : (2283/12500 : ℝ) ^ (107/16 : ℝ) ≤ (576623815427761/50000000000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (2283/12500 : ℝ)) (X := (576623815427761/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 107 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner1 : (50000576623815427761/50000000000000000000 : ℝ) ≤ (625001079859/625000000000 : ℝ) ^ (107/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (625001079859/625000000000 : ℝ)) (X := (50000576623815427761/50000000000000000000 : ℝ)) (by norm_num) 107 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner2 : (25000576623815427761/25000000000000000000 : ℝ) ≤ (312501079859/312500000000 : ℝ) ^ (107/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (312501079859/312500000000 : ℝ)) (X := (25000576623815427761/25000000000000000000 : ℝ)) (by norm_num) 107 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have major0 : P 0 ≤ (X 1 0+X 2 0)+(473/50000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := positive_pair_majorant (p := p) (a := (107/16 : ℝ)) (rho := (2283/12500 : ℝ)) (alpha := (473/50000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      X hmain hsign hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (X 0 1+X 2 1)+(473/50000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := positive_pair_majorant (p := p) (a := (107/16 : ℝ)) (rho := (2283/12500 : ℝ)) (alpha := (473/50000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      X hmain hsign hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (X 0 2+X 1 2)+(473/50000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := positive_pair_majorant (p := p) (a := (107/16 : ℝ)) (rho := (2283/12500 : ℝ)) (alpha := (473/50000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      X hmain hsign hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-510124053/10000000000 : ℝ)*X 0 0+(5400002789/10000000000 : ℝ)*X 0 1+(5400002851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_w036_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5155045951/10000000000 : ℝ)*X 1 0+(-860707711/10000000000 : ℝ)*X 1 1+(1350000711/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_w036_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5155046113/10000000000 : ℝ)*X 2 0+(1080000557/2000000000 : ℝ)*X 2 1+(-860707571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_w036_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((919947551/2000000000 : ℝ)*X 0 0+(3580788751/10000000000 : ℝ)*X 0 1+(3580789087/10000000000 : ℝ)*X 0 2+(919947551/2000000000 : ℝ)*X 1 0+(3580788751/10000000000 : ℝ)*X 1 1+(3580789087/10000000000 : ℝ)*X 1 2+(919947551/2000000000 : ℝ)*X 2 0+(3580788751/10000000000 : ℝ)*X 2 1+(3580789087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_w036_box_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-1404079997/10000000000 : ℝ)*X 0 0+(1267440711/2500000000 : ℝ)*X 0 1+(5069762801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_w036_box_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((5370576389/10000000000 : ℝ)*X 1 0+(-50769773/500000000 : ℝ)*X 1 1+(5069762817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_w036_box_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((671322041/1250000000 : ℝ)*X 2 0+(40558103/80000000 : ℝ)*X 2 1+(-1015395463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_w036_box_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1529350589/5000000000 : ℝ)*X 0 0+(1086524393/2500000000 : ℝ)*X 0 1+(434609749/1000000000 : ℝ)*X 0 2+(1529350589/5000000000 : ℝ)*X 1 0+(1086524393/2500000000 : ℝ)*X 1 1+(434609749/1000000000 : ℝ)*X 1 2+(1529350589/5000000000 : ℝ)*X 2 0+(1086524393/2500000000 : ℝ)*X 2 1+(434609749/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_w036_box_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((-301443/2500000 : ℝ)*X 0 0+(600643341/1250000000 : ℝ)*X 0 1+(1714567/3125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_w036_box_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((5098726147/10000000000 : ℝ)*X 1 0+(-102235809/1250000000 : ℝ)*X 1 1+(5486615681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_w036_box_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp16 : ((5098729297/10000000000 : ℝ)*X 2 0+(5486612321/10000000000 : ℝ)*X 2 1+(-40894341/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_w036_box_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp20 : ((155666277/312500000 : ℝ)*X 0 0+(675806909/2000000000 : ℝ)*X 0 1+(1689516291/5000000000 : ℝ)*X 0 2+(155666277/312500000 : ℝ)*X 1 0+(675806909/2000000000 : ℝ)*X 1 1+(1689516291/5000000000 : ℝ)*X 1 2+(155666277/312500000 : ℝ)*X 2 0+(675806909/2000000000 : ℝ)*X 2 1+(1689516291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_w036_box_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp21 : ((-169004171/2500000000 : ℝ)*X 0 0+(2823103181/5000000000 : ℝ)*X 0 1+(251898979/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_w036_box_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp22 : ((1347865783/2500000000 : ℝ)*X 1 0+(-1029500283/10000000000 : ℝ)*X 1 1+(19679607/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_w036_box_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp23 : ((539146307/1000000000 : ℝ)*X 2 0+(629747453/1250000000 : ℝ)*X 2 1+(-1029500061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_w036_box_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp27 : ((1451041051/5000000000 : ℝ)*X 0 0+(4419299583/10000000000 : ℝ)*X 0 1+(138103121/312500000 : ℝ)*X 0 2+(1451041051/5000000000 : ℝ)*X 1 0+(4419299583/10000000000 : ℝ)*X 1 1+(138103121/312500000 : ℝ)*X 1 2+(1451041051/5000000000 : ℝ)*X 2 0+(4419299583/10000000000 : ℝ)*X 2 1+(138103121/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_w036_box_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-4519/6250 : ℝ) ≤ (-3615054620106819421023/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (2713/125000000000 : ℝ)*(base59) + (1147/50000000000 : ℝ)*(base61) + (13801/250000000000 : ℝ)*(ratio3) + (110319665593/12500000000 : ℝ)*(major0) + (110319665593/12500000000 : ℝ)*(major1) + (110319665593/12500000000 : ℝ)*(major2) + (1004629/1000000000000 : ℝ)*(sp1) + (14503303489883/1000000000000 : ℝ)*(sp7) + (14503302513517/1000000000000 : ℝ)*(sp8) + (14503281919287/1000000000000 : ℝ)*(sp9) + (42360521063/12500000000 : ℝ)*(sp13) + (28263/1000000000000 : ℝ)*(sp14) + (1079943/50000000000 : ℝ)*(sp23) + (493303/100000000000 : ℝ)*(sp27) + (338884661807/100000000000 : ℝ)*(f.failure) + (7251651759073/500000000000 : ℝ)*(f.sum) + (3262751829/10000000000000000000000 : ℝ)*base66 + (293253043/5000000000000000000000 : ℝ)*base68 + (149672757/10000000000000000000000 : ℝ)*base69 + (226814967/625000000000000000000 : ℝ)*base72 + (61574331/10000000000000000000000 : ℝ)*base74 + (2481599/400000000000000000000 : ℝ)*base75 + (1357430129/2500000000000000000000 : ℝ)*base78 + (984384827/2000000000000000000000 : ℝ)*base80 + (1493051581/10000000000000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base87 + (299/1000000000000000 : ℝ)*base90 + (299/1000000000000000 : ℝ)*base92 + (299/1000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59201/100000 : ℝ) ≤ (5920345828375046723337/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (101399/1000000000000 : ℝ)*(base45) + (5353/250000000000 : ℝ)*(base53) + (47717/250000000000 : ℝ)*(ratio0) + (351489/1000000000000 : ℝ)*(ratio4) + (5256376805383/500000000000 : ℝ)*(major0) + (5256376805383/500000000000 : ℝ)*(major1) + (5256376805383/500000000000 : ℝ)*(major2) + (16791469118493/1000000000000 : ℝ)*(sp0) + (16791471652609/1000000000000 : ℝ)*(sp1) + (16791467965563/1000000000000 : ℝ)*(sp2) + (4036688509121/1000000000000 : ℝ)*(sp6) + (1843523/500000000000 : ℝ)*(sp9) + (34357/15625000000 : ℝ)*(sp20) + (633529/250000000000 : ℝ)*(sp21) + (403669070797/100000000000 : ℝ)*(f.failure) + (16791471652609/1000000000000 : ℝ)*(f.sum) + (946901323/5000000000000000000000 : ℝ)*base65 + (26684193/50000000000000000000 : ℝ)*base67 + (3979130357/5000000000000000000000 : ℝ)*base69 + (1822449707/5000000000000000000000 : ℝ)*base71 + (427974573/625000000000000000000 : ℝ)*base73 + (9296415541/10000000000000000000000 : ℝ)*base75 + (2710040933/5000000000000000000000 : ℝ)*base77 + (2344062841/2500000000000000000000 : ℝ)*base79 + (2291737227/2500000000000000000000 : ℝ)*base81 + (271/1000000000000000 : ℝ)*base89 + (271/1000000000000000 : ℝ)*base91 + (271/1000000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (82889/100000 : ℝ) ≤ (8289149964404917357791/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (74433/1000000000000 : ℝ)*(base53) + (49559/125000000000 : ℝ)*(ratio0) + (2414269/1000000000000 : ℝ)*(ratio4) + (1850295548777/200000000000 : ℝ)*(major0) + (1850295548777/200000000000 : ℝ)*(major1) + (1850295548777/200000000000 : ℝ)*(major2) + (15682757/40000000000 : ℝ)*(sp1) + (384223/6250000000 : ℝ)*(sp6) + (992627/31250000000 : ℝ)*(sp7) + (7337115266891/500000000000 : ℝ)*(sp14) + (14673872848517/1000000000000 : ℝ)*(sp15) + (7337132458721/500000000000 : ℝ)*(sp16) + (3552324095831/1000000000000 : ℝ)*(sp20) + (654899/250000000000 : ℝ)*(sp21) + (3552385571511/1000000000000 : ℝ)*(f.failure) + (7337132458721/500000000000 : ℝ)*(f.sum) + (24891429/78125000000000000000 : ℝ)*base66 + (1014490361/10000000000000000000000 : ℝ)*base67 + (2767278727/5000000000000000000000 : ℝ)*base69 + (247028971/5000000000000000000000 : ℝ)*base71 + (1487493219/2500000000000000000000 : ℝ)*base74 + (1220033421/10000000000000000000000 : ℝ)*base75 + (507303171/5000000000000000000000 : ℝ)*base77 + (2997039457/10000000000000000000000 : ℝ)*base80 + (1321843319/5000000000000000000000 : ℝ)*base81 + (10973/10000000000000000 : ℝ)*base89 + (10973/10000000000000000 : ℝ)*base91 + (10973/10000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-12007/12500 : ℝ) ≤ (-9605331393060577206381/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (74729/500000000000 : ℝ)*(base24) + (77169/1000000000000 : ℝ)*(base45) + (7071/62500000000 : ℝ)*(base53) + (7017/250000000000 : ℝ)*(ratio5) + (9975781511571/1000000000000 : ℝ)*(major0) + (9975781511571/1000000000000 : ℝ)*(major1) + (9975781511571/1000000000000 : ℝ)*(major2) + (362309/250000000000 : ℝ)*(sp7) + (43691667/500000000000 : ℝ)*(sp8) + (11420561/1000000000000 : ℝ)*(sp13) + (16441235308361/1000000000000 : ℝ)*(sp21) + (2055143671783/125000000000 : ℝ)*(sp22) + (822061830407/50000000000 : ℝ)*(sp23) + (3830492558079/1000000000000 : ℝ)*(sp27) + (47881299733/12500000000 : ℝ)*(f.failure) + (8220618378799/500000000000 : ℝ)*(f.sum) + (23313/160000000000000000 : ℝ)*base66 + (860264443/2000000000000000000000 : ℝ)*base68 + (1533939797/5000000000000000000000 : ℝ)*base70 + (724904209/1000000000000000000000 : ℝ)*base72 + (2887545397/10000000000000000000000 : ℝ)*base74 + (182806267/312500000000000000000 : ℝ)*base76 + (1630574029/2500000000000000000000 : ℝ)*base78 + (6758881709/10000000000000000000000 : ℝ)*base80 + (289285981/5000000000000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base84 + (9/7812500000000 : ℝ)*base89 + (9/7812500000000 : ℝ)*base91 + (9/7812500000000 : ℝ)*base93 + hcertificate_margin
theorem positive_w036_box (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26043/10000 : ℝ) (148023/100000 : ℝ) (84849/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2283/12500 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(4519/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59201/100000 : ℝ) else (82889/100000 : ℝ) ≤ X j i ∧ X j i ≤ (12007/12500 : ℝ) := by
  exact frame_box_of_base (base_w036_box p hpa hpb) X hX hsign hratio

end HlawkaSchatten.DiagonalCutoff6


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem solution (p : ℝ) (hpa : (107/16 : ℝ) ≤ p) (hpb : p ≤ (215/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26043/10000 : ℝ) (148023/100000 : ℝ) (84849/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2283/12500 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(4519/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59201/100000 : ℝ) else (82889/100000 : ℝ) ≤ X j i ∧ X j i ≤ (12007/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff6.positive_w036_box p hpa hpb X hX hsign hratio

#print axioms solution
