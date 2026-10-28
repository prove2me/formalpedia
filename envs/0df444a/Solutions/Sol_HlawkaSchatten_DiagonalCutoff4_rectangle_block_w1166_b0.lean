-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1166_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:42:30.415925+00:00
-- url     : https://prove2.me/submissions/a0b1d052-4074-4523-8e02-1e894fd878f2

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
theorem support_rectangle_w1166_s0_0 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1884238029/10000000000 : ℝ)*x 0 + (6048799729/10000000000 : ℝ)*x 1 + (4783500121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1884238029/10000000000 : ℝ)^8359 ≤ (10962461330849/100000000000000 : ℝ)^6311 := by
    have hnat : (1884238029 : ℕ)^8359*100000000000000^6311 ≤ 10962461330849^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884238029 10000000000 10962461330849 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6048799729/10000000000 : ℝ)^8359 ≤ (51382836834891/100000000000000 : ℝ)^6311 := by
    have hnat : (6048799729 : ℕ)^8359*100000000000000^6311 ≤ 51382836834891^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6048799729 10000000000 51382836834891 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4783500121/10000000000 : ℝ)^8359 ≤ (37654701823637/100000000000000 : ℝ)^6311 := by
    have hnat : (4783500121 : ℕ)^8359*100000000000000^6311 ≤ 37654701823637^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783500121 10000000000 37654701823637 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1884238029/10000000000 : ℝ), (6048799729/10000000000 : ℝ), (4783500121/10000000000 : ℝ)] ![(10962461330849/100000000000000 : ℝ), (51382836834891/100000000000000 : ℝ), (37654701823637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1884238029/10000000000 : ℝ)|^8359 ≤ (10962461330849/100000000000000 : ℝ)^6311
        have hw : |(-1884238029/10000000000 : ℝ)|=(1884238029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6048799729/10000000000 : ℝ)|^8359 ≤ (51382836834891/100000000000000 : ℝ)^6311
        have hw : |(6048799729/10000000000 : ℝ)|=(6048799729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4783500121/10000000000 : ℝ)|^8359 ≤ (37654701823637/100000000000000 : ℝ)^6311
        have hw : |(4783500121/10000000000 : ℝ)|=(4783500121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s0_1 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5515441611/10000000000 : ℝ)*x 0 + (-1304846739/5000000000 : ℝ)*x 1 + (4783500093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515441611/10000000000 : ℝ)^8359 ≤ (22734730159843/50000000000000 : ℝ)^6311 := by
    have hnat : (5515441611 : ℕ)^8359*50000000000000^6311 ≤ 22734730159843^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515441611 10000000000 22734730159843 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304846739/5000000000 : ℝ)^8359 ≤ (16875838140233/100000000000000 : ℝ)^6311 := by
    have hnat : (1304846739 : ℕ)^8359*100000000000000^6311 ≤ 16875838140233^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304846739 5000000000 16875838140233 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4783500093/10000000000 : ℝ)^8359 ≤ (37654701531701/100000000000000 : ℝ)^6311 := by
    have hnat : (4783500093 : ℕ)^8359*100000000000000^6311 ≤ 37654701531701^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783500093 10000000000 37654701531701 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515441611/10000000000 : ℝ), (-1304846739/5000000000 : ℝ), (4783500093/10000000000 : ℝ)] ![(22734730159843/50000000000000 : ℝ), (16875838140233/100000000000000 : ℝ), (37654701531701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515441611/10000000000 : ℝ)|^8359 ≤ (22734730159843/50000000000000 : ℝ)^6311
        have hw : |(5515441611/10000000000 : ℝ)|=(5515441611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1304846739/5000000000 : ℝ)|^8359 ≤ (16875838140233/100000000000000 : ℝ)^6311
        have hw : |(-1304846739/5000000000 : ℝ)|=(1304846739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4783500093/10000000000 : ℝ)|^8359 ≤ (37654701531701/100000000000000 : ℝ)^6311
        have hw : |(4783500093/10000000000 : ℝ)|=(4783500093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s0_2 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757720783/5000000000 : ℝ)*x 0 + (956700029/2000000000 : ℝ)*x 1 + (-2609693471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757720783/5000000000 : ℝ)^8359 ≤ (45469459828317/100000000000000 : ℝ)^6311 := by
    have hnat : (2757720783 : ℕ)^8359*100000000000000^6311 ≤ 45469459828317^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757720783 5000000000 45469459828317 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956700029/2000000000 : ℝ)^8359 ≤ (9413675518467/25000000000000 : ℝ)^6311 := by
    have hnat : (956700029 : ℕ)^8359*25000000000000^6311 ≤ 9413675518467^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956700029 2000000000 9413675518467 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609693471/10000000000 : ℝ)^8359 ≤ (8437919040139/50000000000000 : ℝ)^6311 := by
    have hnat : (2609693471 : ℕ)^8359*50000000000000^6311 ≤ 8437919040139^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609693471 10000000000 8437919040139 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757720783/5000000000 : ℝ), (956700029/2000000000 : ℝ), (-2609693471/10000000000 : ℝ)] ![(45469459828317/100000000000000 : ℝ), (9413675518467/25000000000000 : ℝ), (8437919040139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757720783/5000000000 : ℝ)|^8359 ≤ (45469459828317/100000000000000 : ℝ)^6311
        have hw : |(2757720783/5000000000 : ℝ)|=(2757720783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(956700029/2000000000 : ℝ)|^8359 ≤ (9413675518467/25000000000000 : ℝ)^6311
        have hw : |(956700029/2000000000 : ℝ)|=(956700029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2609693471/10000000000 : ℝ)|^8359 ≤ (8437919040139/50000000000000 : ℝ)^6311
        have hw : |(-2609693471/10000000000 : ℝ)|=(2609693471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s0_3 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1049764179/2500000000 : ℝ)*x 0 + (3119992741/10000000000 : ℝ)*x 1 + (1412282241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049764179/2500000000 : ℝ)^8359 ≤ (15842717491401/50000000000000 : ℝ)^6311 := by
    have hnat : (1049764179 : ℕ)^8359*50000000000000^6311 ≤ 15842717491401^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049764179 2500000000 15842717491401 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3119992741/10000000000 : ℝ)^8359 ≤ (21379619375507/100000000000000 : ℝ)^6311 := by
    have hnat : (3119992741 : ℕ)^8359*100000000000000^6311 ≤ 21379619375507^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119992741 10000000000 21379619375507 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1412282241/2500000000 : ℝ)^8359 ≤ (11733736406057/25000000000000 : ℝ)^6311 := by
    have hnat : (1412282241 : ℕ)^8359*25000000000000^6311 ≤ 11733736406057^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412282241 2500000000 11733736406057 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049764179/2500000000 : ℝ), (3119992741/10000000000 : ℝ), (1412282241/2500000000 : ℝ)] ![(15842717491401/50000000000000 : ℝ), (21379619375507/100000000000000 : ℝ), (11733736406057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049764179/2500000000 : ℝ)|^8359 ≤ (15842717491401/50000000000000 : ℝ)^6311
        have hw : |(1049764179/2500000000 : ℝ)|=(1049764179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3119992741/10000000000 : ℝ)|^8359 ≤ (21379619375507/100000000000000 : ℝ)^6311
        have hw : |(3119992741/10000000000 : ℝ)|=(3119992741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1412282241/2500000000 : ℝ)|^8359 ≤ (11733736406057/25000000000000 : ℝ)^6311
        have hw : |(1412282241/2500000000 : ℝ)|=(1412282241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s0_4 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-944656667/5000000000 : ℝ)*x 0 + (1204032231/2500000000 : ℝ)*x 1 + (6015022013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (944656667/5000000000 : ℝ)^8359 ≤ (2750397166079/25000000000000 : ℝ)^6311 := by
    have hnat : (944656667 : ℕ)^8359*25000000000000^6311 ≤ 2750397166079^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944656667 5000000000 2750397166079 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204032231/2500000000 : ℝ)^8359 ≤ (18997637473883/50000000000000 : ℝ)^6311 := by
    have hnat : (1204032231 : ℕ)^8359*50000000000000^6311 ≤ 18997637473883^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204032231 2500000000 18997637473883 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6015022013/10000000000 : ℝ)^8359 ≤ (51003136377529/100000000000000 : ℝ)^6311 := by
    have hnat : (6015022013 : ℕ)^8359*100000000000000^6311 ≤ 51003136377529^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015022013 10000000000 51003136377529 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-944656667/5000000000 : ℝ), (1204032231/2500000000 : ℝ), (6015022013/10000000000 : ℝ)] ![(2750397166079/25000000000000 : ℝ), (18997637473883/50000000000000 : ℝ), (51003136377529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-944656667/5000000000 : ℝ)|^8359 ≤ (2750397166079/25000000000000 : ℝ)^6311
        have hw : |(-944656667/5000000000 : ℝ)|=(944656667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204032231/2500000000 : ℝ)|^8359 ≤ (18997637473883/50000000000000 : ℝ)^6311
        have hw : |(1204032231/2500000000 : ℝ)|=(1204032231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6015022013/10000000000 : ℝ)|^8359 ≤ (51003136377529/100000000000000 : ℝ)^6311
        have hw : |(6015022013/10000000000 : ℝ)|=(6015022013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s0_5 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171515741/10000000000 : ℝ)*x 0 + (-689085899/5000000000 : ℝ)*x 1 + (3007510897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171515741/10000000000 : ℝ)^8359 ≤ (41752567864261/100000000000000 : ℝ)^6311 := by
    have hnat : (5171515741 : ℕ)^8359*100000000000000^6311 ≤ 41752567864261^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171515741 10000000000 41752567864261 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689085899/5000000000 : ℝ)^8359 ≤ (3622149106103/50000000000000 : ℝ)^6311 := by
    have hnat : (689085899 : ℕ)^8359*50000000000000^6311 ≤ 3622149106103^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689085899 5000000000 3622149106103 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3007510897/5000000000 : ℝ)^8359 ≤ (10200626783591/20000000000000 : ℝ)^6311 := by
    have hnat : (3007510897 : ℕ)^8359*20000000000000^6311 ≤ 10200626783591^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007510897 5000000000 10200626783591 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171515741/10000000000 : ℝ), (-689085899/5000000000 : ℝ), (3007510897/5000000000 : ℝ)] ![(41752567864261/100000000000000 : ℝ), (3622149106103/50000000000000 : ℝ), (10200626783591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171515741/10000000000 : ℝ)|^8359 ≤ (41752567864261/100000000000000 : ℝ)^6311
        have hw : |(5171515741/10000000000 : ℝ)|=(5171515741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-689085899/5000000000 : ℝ)|^8359 ≤ (3622149106103/50000000000000 : ℝ)^6311
        have hw : |(-689085899/5000000000 : ℝ)|=(689085899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3007510897/5000000000 : ℝ)|^8359 ≤ (10200626783591/20000000000000 : ℝ)^6311
        have hw : |(3007510897/5000000000 : ℝ)|=(3007510897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s0_6 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292878927/2500000000 : ℝ)*x 0 + (1203004377/2000000000 : ℝ)*x 1 + (-1378171701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292878927/2500000000 : ℝ)^8359 ≤ (334020540091/800000000000 : ℝ)^6311 := by
    have hnat : (1292878927 : ℕ)^8359*800000000000^6311 ≤ 334020540091^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292878927 2500000000 334020540091 800000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203004377/2000000000 : ℝ)^8359 ≤ (5100313493997/10000000000000 : ℝ)^6311 := by
    have hnat : (1203004377 : ℕ)^8359*10000000000000^6311 ≤ 5100313493997^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203004377 2000000000 5100313493997 10000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378171701/10000000000 : ℝ)^8359 ≤ (7244297536869/100000000000000 : ℝ)^6311 := by
    have hnat : (1378171701 : ℕ)^8359*100000000000000^6311 ≤ 7244297536869^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378171701 10000000000 7244297536869 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292878927/2500000000 : ℝ), (1203004377/2000000000 : ℝ), (-1378171701/10000000000 : ℝ)] ![(334020540091/800000000000 : ℝ), (5100313493997/10000000000000 : ℝ), (7244297536869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292878927/2500000000 : ℝ)|^8359 ≤ (334020540091/800000000000 : ℝ)^6311
        have hw : |(1292878927/2500000000 : ℝ)|=(1292878927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203004377/2000000000 : ℝ)|^8359 ≤ (5100313493997/10000000000000 : ℝ)^6311
        have hw : |(1203004377/2000000000 : ℝ)|=(1203004377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1378171701/10000000000 : ℝ)|^8359 ≤ (7244297536869/100000000000000 : ℝ)^6311
        have hw : |(-1378171701/10000000000 : ℝ)|=(1378171701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s0_7 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4209201699/10000000000 : ℝ)*x 0 + (5583908869/10000000000 : ℝ)*x 1 + (318750933/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209201699/10000000000 : ℝ)^8359 ≤ (31786869443663/100000000000000 : ℝ)^6311 := by
    have hnat : (4209201699 : ℕ)^8359*100000000000000^6311 ≤ 31786869443663^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209201699 10000000000 31786869443663 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5583908869/10000000000 : ℝ)^8359 ≤ (46218577989401/100000000000000 : ℝ)^6311 := by
    have hnat : (5583908869 : ℕ)^8359*100000000000000^6311 ≤ 46218577989401^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5583908869 10000000000 46218577989401 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318750933/1000000000 : ℝ)^8359 ≤ (5498638136711/25000000000000 : ℝ)^6311 := by
    have hnat : (318750933 : ℕ)^8359*25000000000000^6311 ≤ 5498638136711^6311*1000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318750933 1000000000 5498638136711 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209201699/10000000000 : ℝ), (5583908869/10000000000 : ℝ), (318750933/1000000000 : ℝ)] ![(31786869443663/100000000000000 : ℝ), (46218577989401/100000000000000 : ℝ), (5498638136711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209201699/10000000000 : ℝ)|^8359 ≤ (31786869443663/100000000000000 : ℝ)^6311
        have hw : |(4209201699/10000000000 : ℝ)|=(4209201699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5583908869/10000000000 : ℝ)|^8359 ≤ (46218577989401/100000000000000 : ℝ)^6311
        have hw : |(5583908869/10000000000 : ℝ)|=(5583908869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318750933/1000000000 : ℝ)|^8359 ≤ (5498638136711/25000000000000 : ℝ)^6311
        have hw : |(318750933/1000000000 : ℝ)|=(318750933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1166_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (16/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27723/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4179/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4179 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4179*1^1024 ≤ 0^1024*1^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4179/1024 : ℝ) ≤ (2376758535645355977/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4179 ≤ (2376758535645355977/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4179*100000000000000000000^1024 ≤ 2376758535645355977^1024*5^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2376758535645355977 100000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2376758535645355977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4179 := by
      have hnat : (1 : ℕ)^1024*1^4179 ≤ 1^4179*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102376758535645355977/100000000000000000000 : ℝ) ≤ (10057723468728629/10000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (102376758535645355977/100000000000000000000 : ℝ)^1024 ≤ (10057723468728629/10000000000000000 : ℝ)^4179 := by
      have hnat : (102376758535645355977 : ℕ)^1024*10000000000000000^4179 ≤ 10057723468728629^4179*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102376758535645355977 100000000000000000000 10057723468728629 10000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057723468728629/10000000000000000 : ℝ)) (X := (102376758535645355977/100000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52376758535645355977/50000000000000000000 : ℝ) ≤ (5057723468728629/5000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (52376758535645355977/50000000000000000000 : ℝ)^1024 ≤ (5057723468728629/5000000000000000 : ℝ)^4179 := by
      have hnat : (52376758535645355977 : ℕ)^1024*5000000000000000^4179 ≤ 5057723468728629^4179*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52376758535645355977 50000000000000000000 5057723468728629 5000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057723468728629/5000000000000000 : ℝ)) (X := (52376758535645355977/50000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57723468728629/4000000000000000 : ℝ)*(0 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(57723468728629/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2376758535645355977/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57723468728629/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4179/1024 : ℝ) := by
    rw [show (1 : ℝ)+(57723468728629/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057723468728629/10000000000000000 : ℝ) by norm_num, show 1+(2376758535645355977/100000000000000000000 : ℝ)+(0 : ℝ)=(102376758535645355977/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2376758535645355977/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57723468728629/4000000000000000 : ℝ)*(2/5 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(57723468728629/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057723468728629/5000000000000000 : ℝ) by norm_num, show 1+2*(2376758535645355977/100000000000000000000 : ℝ)=(52376758535645355977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57723468728629/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57723468728629/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57723468728629/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57723468728629/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57723468728629/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57723468728629/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1884238029/10000000000 : ℝ)*X 0 0+(6048799729/10000000000 : ℝ)*X 0 1+(4783500121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5515441611/10000000000 : ℝ)*X 1 0+(-1304846739/5000000000 : ℝ)*X 1 1+(4783500093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757720783/5000000000 : ℝ)*X 2 0+(956700029/2000000000 : ℝ)*X 2 1+(-2609693471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1049764179/2500000000 : ℝ)*X 0 0+(3119992741/10000000000 : ℝ)*X 0 1+(1412282241/2500000000 : ℝ)*X 0 2+(1049764179/2500000000 : ℝ)*X 1 0+(3119992741/10000000000 : ℝ)*X 1 1+(1412282241/2500000000 : ℝ)*X 1 2+(1049764179/2500000000 : ℝ)*X 2 0+(3119992741/10000000000 : ℝ)*X 2 1+(1412282241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-944656667/5000000000 : ℝ)*X 0 0+(1204032231/2500000000 : ℝ)*X 0 1+(6015022013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171515741/10000000000 : ℝ)*X 1 0+(-689085899/5000000000 : ℝ)*X 1 1+(3007510897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292878927/2500000000 : ℝ)*X 2 0+(1203004377/2000000000 : ℝ)*X 2 1+(-1378171701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4209201699/10000000000 : ℝ)*X 0 0+(5583908869/10000000000 : ℝ)*X 0 1+(318750933/1000000000 : ℝ)*X 0 2+(4209201699/10000000000 : ℝ)*X 1 0+(5583908869/10000000000 : ℝ)*X 1 1+(318750933/1000000000 : ℝ)*X 1 2+(4209201699/10000000000 : ℝ)*X 2 0+(5583908869/10000000000 : ℝ)*X 2 1+(318750933/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (375643792390926348372699/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35020241/100000000000000 : ℝ)*(base1) + (950820511/100000000000000 : ℝ)*(base19) + (219985563/25000000000000 : ℝ)*(base23) + (32215009/50000000000000 : ℝ)*(base24) + (215406001/100000000000000 : ℝ)*(upper3) + (592863340071241/100000000000000 : ℝ)*(major0) + (592863340071241/100000000000000 : ℝ)*(major1) + (592863340071241/100000000000000 : ℝ)*(major2) + (395164930830203/50000000000000 : ℝ)*(sp0) + (395165500110381/50000000000000 : ℝ)*(sp1) + (790331006669003/100000000000000 : ℝ)*(sp2) + (395392899005053/100000000000000 : ℝ)*(sp3) + (531100277/25000000000000 : ℝ)*(sp4) + (26091583/1562500000000 : ℝ)*(sp7) + (197697301943303/50000000000000 : ℝ)*(f.failure) + (790331951041273/100000000000000 : ℝ)*(f.sum) + (239236318258589/200000000000000000000000000000 : ℝ)*base65 + (308846889458589/400000000000000000000000000000 : ℝ)*base67 + (1654518323458589/400000000000000000000000000000 : ℝ)*base69 + (818883509058589/400000000000000000000000000000 : ℝ)*base71 + (338695323258589/200000000000000000000000000000 : ℝ)*base73 + (204905789058589/400000000000000000000000000000 : ℝ)*base75 + (247263062658589/400000000000000000000000000000 : ℝ)*base77 + (1069555821858589/400000000000000000000000000000 : ℝ)*base79 + (1039493228458589/200000000000000000000000000000 : ℝ)*base81 + (36516521/5000000000000000000000 : ℝ)*base90 + (36516521/5000000000000000000000 : ℝ)*base92 + (36516521/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70025835189444050533983/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5046437/12500000000000 : ℝ)*(base1) + (22004541/3125000000000 : ℝ)*(base19) + (139862679/20000000000000 : ℝ)*(base23) + (68933343/100000000000000 : ℝ)*(upper3) + (87721259/100000000000000 : ℝ)*(upper5) + (312848894071991/50000000000000 : ℝ)*(major0) + (312848894071991/50000000000000 : ℝ)*(major1) + (312848894071991/50000000000000 : ℝ)*(major2) + (1373233079/100000000000000 : ℝ)*(sp1) + (690304909/50000000000000 : ℝ)*(sp2) + (834102848277923/100000000000000 : ℝ)*(sp4) + (208525182632009/25000000000000 : ℝ)*(sp5) + (417050363991607/50000000000000 : ℝ)*(sp6) + (83458526928451/20000000000000 : ℝ)*(sp7) + (417292675013751/100000000000000 : ℝ)*(f.failure) + (834102807906427/100000000000000 : ℝ)*(f.sum) + (24876972430339/100000000000000000000000000000 : ℝ)*base65 + (561502679330339/200000000000000000000000000000 : ℝ)*base67 + (936691938930339/200000000000000000000000000000 : ℝ)*base69 + (951572330730339/200000000000000000000000000000 : ℝ)*base71 + (4273641769661/100000000000000000000000000000 : ℝ)*base74 + (379037152530339/200000000000000000000000000000 : ℝ)*base75 + (941141219730339/200000000000000000000000000000 : ℝ)*base77 + (528879249730339/200000000000000000000000000000 : ℝ)*base79 + (73642182930339/100000000000000000000000000000 : ℝ)*base81 + (69904057/10000000000000000000000 : ℝ)*base90 + (69904057/10000000000000000000000 : ℝ)*base92 + (69904057/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1166_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (16/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27723/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1166_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1166_s1_0 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087168531/10000000000 : ℝ)*x 0 + (5695132703/10000000000 : ℝ)*x 1 + (1001451873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087168531/10000000000 : ℝ)^8359 ≤ (3138233557399/25000000000000 : ℝ)^6311 := by
    have hnat : (2087168531 : ℕ)^8359*25000000000000^6311 ≤ 3138233557399^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087168531 10000000000 3138233557399 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5695132703/10000000000 : ℝ)^8359 ≤ (5930232780271/12500000000000 : ℝ)^6311 := by
    have hnat : (5695132703 : ℕ)^8359*12500000000000^6311 ≤ 5930232780271^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5695132703 10000000000 5930232780271 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001451873/2000000000 : ℝ)^8359 ≤ (10001300879041/25000000000000 : ℝ)^6311 := by
    have hnat : (1001451873 : ℕ)^8359*25000000000000^6311 ≤ 10001300879041^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001451873 2000000000 10001300879041 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087168531/10000000000 : ℝ), (5695132703/10000000000 : ℝ), (1001451873/2000000000 : ℝ)] ![(3138233557399/25000000000000 : ℝ), (5930232780271/12500000000000 : ℝ), (10001300879041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087168531/10000000000 : ℝ)|^8359 ≤ (3138233557399/25000000000000 : ℝ)^6311
        have hw : |(-2087168531/10000000000 : ℝ)|=(2087168531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5695132703/10000000000 : ℝ)|^8359 ≤ (5930232780271/12500000000000 : ℝ)^6311
        have hw : |(5695132703/10000000000 : ℝ)|=(5695132703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001451873/2000000000 : ℝ)|^8359 ≤ (10001300879041/25000000000000 : ℝ)^6311
        have hw : |(1001451873/2000000000 : ℝ)|=(1001451873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s1_1 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417803561/10000000000 : ℝ)*x 0 + (-245793153/1000000000 : ℝ)*x 1 + (2503629203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417803561/10000000000 : ℝ)^8359 ≤ (1776255748491/4000000000000 : ℝ)^6311 := by
    have hnat : (5417803561 : ℕ)^8359*4000000000000^6311 ≤ 1776255748491^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417803561 10000000000 1776255748491 4000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245793153/1000000000 : ℝ)^8359 ≤ (7794206453997/50000000000000 : ℝ)^6311 := by
    have hnat : (245793153 : ℕ)^8359*50000000000000^6311 ≤ 7794206453997^6311*1000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245793153 1000000000 7794206453997 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2503629203/5000000000 : ℝ)^8359 ≤ (20002596683957/50000000000000 : ℝ)^6311 := by
    have hnat : (2503629203 : ℕ)^8359*50000000000000^6311 ≤ 20002596683957^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503629203 5000000000 20002596683957 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417803561/10000000000 : ℝ), (-245793153/1000000000 : ℝ), (2503629203/5000000000 : ℝ)] ![(1776255748491/4000000000000 : ℝ), (7794206453997/50000000000000 : ℝ), (20002596683957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417803561/10000000000 : ℝ)|^8359 ≤ (1776255748491/4000000000000 : ℝ)^6311
        have hw : |(5417803561/10000000000 : ℝ)|=(5417803561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245793153/1000000000 : ℝ)|^8359 ≤ (7794206453997/50000000000000 : ℝ)^6311
        have hw : |(-245793153/1000000000 : ℝ)|=(245793153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2503629203/5000000000 : ℝ)|^8359 ≤ (20002596683957/50000000000000 : ℝ)^6311
        have hw : |(2503629203/5000000000 : ℝ)|=(2503629203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s1_2 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417805677/10000000000 : ℝ)*x 0 + (250362823/500000000 : ℝ)*x 1 + (-2457931247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417805677/10000000000 : ℝ)^8359 ≤ (22203208342013/50000000000000 : ℝ)^6311 := by
    have hnat : (5417805677 : ℕ)^8359*50000000000000^6311 ≤ 22203208342013^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417805677 10000000000 22203208342013 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250362823/500000000 : ℝ)^8359 ≤ (20002586387559/50000000000000 : ℝ)^6311 := by
    have hnat : (250362823 : ℕ)^8359*50000000000000^6311 ≤ 20002586387559^6311*500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250362823 500000000 20002586387559 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2457931247/10000000000 : ℝ)^8359 ≤ (3117682106149/20000000000000 : ℝ)^6311 := by
    have hnat : (2457931247 : ℕ)^8359*20000000000000^6311 ≤ 3117682106149^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457931247 10000000000 3117682106149 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417805677/10000000000 : ℝ), (250362823/500000000 : ℝ), (-2457931247/10000000000 : ℝ)] ![(22203208342013/50000000000000 : ℝ), (20002586387559/50000000000000 : ℝ), (3117682106149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417805677/10000000000 : ℝ)|^8359 ≤ (22203208342013/50000000000000 : ℝ)^6311
        have hw : |(5417805677/10000000000 : ℝ)|=(5417805677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250362823/500000000 : ℝ)|^8359 ≤ (20002586387559/50000000000000 : ℝ)^6311
        have hw : |(250362823/500000000 : ℝ)|=(250362823/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2457931247/10000000000 : ℝ)|^8359 ≤ (3117682106149/20000000000000 : ℝ)^6311
        have hw : |(-2457931247/10000000000 : ℝ)|=(2457931247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s1_3 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2157701227/5000000000 : ℝ)*x 0 + (460192761/1250000000 : ℝ)*x 1 + (5056488637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157701227/5000000000 : ℝ)^8359 ≤ (205334100129/625000000000 : ℝ)^6311 := by
    have hnat : (2157701227 : ℕ)^8359*625000000000^6311 ≤ 205334100129^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157701227 5000000000 205334100129 625000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460192761/1250000000 : ℝ)^8359 ≤ (2661956134167/10000000000000 : ℝ)^6311 := by
    have hnat : (460192761 : ℕ)^8359*10000000000000^6311 ≤ 2661956134167^6311*1250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460192761 1250000000 2661956134167 10000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5056488637/10000000000 : ℝ)^8359 ≤ (40526982617787/100000000000000 : ℝ)^6311 := by
    have hnat : (5056488637 : ℕ)^8359*100000000000000^6311 ≤ 40526982617787^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056488637 10000000000 40526982617787 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157701227/5000000000 : ℝ), (460192761/1250000000 : ℝ), (5056488637/10000000000 : ℝ)] ![(205334100129/625000000000 : ℝ), (2661956134167/10000000000000 : ℝ), (40526982617787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157701227/5000000000 : ℝ)|^8359 ≤ (205334100129/625000000000 : ℝ)^6311
        have hw : |(2157701227/5000000000 : ℝ)|=(2157701227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(460192761/1250000000 : ℝ)|^8359 ≤ (2661956134167/10000000000000 : ℝ)^6311
        have hw : |(460192761/1250000000 : ℝ)|=(460192761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5056488637/10000000000 : ℝ)|^8359 ≤ (40526982617787/100000000000000 : ℝ)^6311
        have hw : |(5056488637/10000000000 : ℝ)|=(5056488637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s1_4 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-521986479/2500000000 : ℝ)*x 0 + (5016565699/10000000000 : ℝ)*x 1 + (2842820277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521986479/2500000000 : ℝ)^8359 ≤ (6279563651873/50000000000000 : ℝ)^6311 := by
    have hnat : (521986479 : ℕ)^8359*50000000000000^6311 ≤ 6279563651873^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521986479 2500000000 6279563651873 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5016565699/10000000000 : ℝ)^8359 ≤ (20051856956677/50000000000000 : ℝ)^6311 := by
    have hnat : (5016565699 : ℕ)^8359*50000000000000^6311 ≤ 20051856956677^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5016565699 10000000000 20051856956677 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842820277/5000000000 : ℝ)^8359 ≤ (9467431754983/20000000000000 : ℝ)^6311 := by
    have hnat : (2842820277 : ℕ)^8359*20000000000000^6311 ≤ 9467431754983^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842820277 5000000000 9467431754983 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-521986479/2500000000 : ℝ), (5016565699/10000000000 : ℝ), (2842820277/5000000000 : ℝ)] ![(6279563651873/50000000000000 : ℝ), (20051856956677/50000000000000 : ℝ), (9467431754983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-521986479/2500000000 : ℝ)|^8359 ≤ (6279563651873/50000000000000 : ℝ)^6311
        have hw : |(-521986479/2500000000 : ℝ)|=(521986479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5016565699/10000000000 : ℝ)|^8359 ≤ (20051856956677/50000000000000 : ℝ)^6311
        have hw : |(5016565699/10000000000 : ℝ)|=(5016565699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2842820277/5000000000 : ℝ)|^8359 ≤ (9467431754983/20000000000000 : ℝ)^6311
        have hw : |(2842820277/5000000000 : ℝ)|=(2842820277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s1_5 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5241234539/10000000000 : ℝ)*x 0 + (-1779546081/10000000000 : ℝ)*x 1 + (5685643657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241234539/10000000000 : ℝ)^8359 ≤ (5312466811307/12500000000000 : ℝ)^6311 := by
    have hnat : (5241234539 : ℕ)^8359*12500000000000^6311 ≤ 5312466811307^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241234539 10000000000 5312466811307 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1779546081/10000000000 : ℝ)^8359 ≤ (1270384062347/12500000000000 : ℝ)^6311 := by
    have hnat : (1779546081 : ℕ)^8359*12500000000000^6311 ≤ 1270384062347^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779546081 10000000000 1270384062347 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5685643657/10000000000 : ℝ)^8359 ≤ (23668596496699/50000000000000 : ℝ)^6311 := by
    have hnat : (5685643657 : ℕ)^8359*50000000000000^6311 ≤ 23668596496699^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5685643657 10000000000 23668596496699 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241234539/10000000000 : ℝ), (-1779546081/10000000000 : ℝ), (5685643657/10000000000 : ℝ)] ![(5312466811307/12500000000000 : ℝ), (1270384062347/12500000000000 : ℝ), (23668596496699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241234539/10000000000 : ℝ)|^8359 ≤ (5312466811307/12500000000000 : ℝ)^6311
        have hw : |(5241234539/10000000000 : ℝ)|=(5241234539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1779546081/10000000000 : ℝ)|^8359 ≤ (1270384062347/12500000000000 : ℝ)^6311
        have hw : |(-1779546081/10000000000 : ℝ)|=(1779546081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5685643657/10000000000 : ℝ)|^8359 ≤ (23668596496699/50000000000000 : ℝ)^6311
        have hw : |(5685643657/10000000000 : ℝ)|=(5685643657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s1_6 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620616857/5000000000 : ℝ)*x 0 + (568564501/1000000000 : ℝ)*x 1 + (-1779545281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620616857/5000000000 : ℝ)^8359 ≤ (8499945125973/20000000000000 : ℝ)^6311 := by
    have hnat : (2620616857 : ℕ)^8359*20000000000000^6311 ≤ 8499945125973^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620616857 5000000000 8499945125973 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568564501/1000000000 : ℝ)^8359 ≤ (5917150989209/12500000000000 : ℝ)^6311 := by
    have hnat : (568564501 : ℕ)^8359*12500000000000^6311 ≤ 5917150989209^6311*1000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568564501 1000000000 5917150989209 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1779545281/10000000000 : ℝ)^8359 ≤ (2540766611823/25000000000000 : ℝ)^6311 := by
    have hnat : (1779545281 : ℕ)^8359*25000000000000^6311 ≤ 2540766611823^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779545281 10000000000 2540766611823 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620616857/5000000000 : ℝ), (568564501/1000000000 : ℝ), (-1779545281/10000000000 : ℝ)] ![(8499945125973/20000000000000 : ℝ), (5917150989209/12500000000000 : ℝ), (2540766611823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620616857/5000000000 : ℝ)|^8359 ≤ (8499945125973/20000000000000 : ℝ)^6311
        have hw : |(2620616857/5000000000 : ℝ)|=(2620616857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568564501/1000000000 : ℝ)|^8359 ≤ (5917150989209/12500000000000 : ℝ)^6311
        have hw : |(568564501/1000000000 : ℝ)|=(568564501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1779545281/10000000000 : ℝ)|^8359 ≤ (2540766611823/25000000000000 : ℝ)^6311
        have hw : |(-1779545281/10000000000 : ℝ)|=(1779545281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s1_7 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4316944583/10000000000 : ℝ)*x 0 + (125947233/250000000 : ℝ)*x 1 + (1850253463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316944583/10000000000 : ℝ)^8359 ≤ (328690071447/1000000000000 : ℝ)^6311 := by
    have hnat : (4316944583 : ℕ)^8359*1000000000000^6311 ≤ 328690071447^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316944583 10000000000 328690071447 1000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125947233/250000000 : ℝ)^8359 ≤ (40329654540589/100000000000000 : ℝ)^6311 := by
    have hnat : (125947233 : ℕ)^8359*100000000000000^6311 ≤ 40329654540589^6311*250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125947233 250000000 40329654540589 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1850253463/5000000000 : ℝ)^8359 ≤ (6700334575273/25000000000000 : ℝ)^6311 := by
    have hnat : (1850253463 : ℕ)^8359*25000000000000^6311 ≤ 6700334575273^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850253463 5000000000 6700334575273 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316944583/10000000000 : ℝ), (125947233/250000000 : ℝ), (1850253463/5000000000 : ℝ)] ![(328690071447/1000000000000 : ℝ), (40329654540589/100000000000000 : ℝ), (6700334575273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316944583/10000000000 : ℝ)|^8359 ≤ (328690071447/1000000000000 : ℝ)^6311
        have hw : |(4316944583/10000000000 : ℝ)|=(4316944583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125947233/250000000 : ℝ)|^8359 ≤ (40329654540589/100000000000000 : ℝ)^6311
        have hw : |(125947233/250000000 : ℝ)|=(125947233/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1850253463/5000000000 : ℝ)|^8359 ≤ (6700334575273/25000000000000 : ℝ)^6311
        have hw : |(1850253463/5000000000 : ℝ)|=(1850253463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1166_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (16/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5783/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20329/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (16/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (16/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (16/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (16/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (16/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (16/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (16/3125 : ℝ) ^ (4179/1024 : ℝ) ≤ (8962629259/20000000000000000000 : ℝ) := by
    have hpowers : (16/3125 : ℝ)^4179 ≤ (8962629259/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16 : ℕ)^4179*20000000000000000000^1024 ≤ 8962629259^1024*3125^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16 3125 8962629259 20000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16/3125 : ℝ)) (X := (8962629259/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27723/100000 : ℝ) ^ (4179/1024 : ℝ) ≤ (532353959286857647/100000000000000000000 : ℝ) := by
    have hpowers : (27723/100000 : ℝ)^4179 ≤ (532353959286857647/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27723 : ℕ)^4179*100000000000000000000^1024 ≤ 532353959286857647^1024*100000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27723 100000 532353959286857647 100000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27723/100000 : ℝ)) (X := (532353959286857647/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000008962629259/10000000000000000000 : ℝ) ≤ (2500000000549039/2500000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (10000000008962629259/10000000000000000000 : ℝ)^1024 ≤ (2500000000549039/2500000000000000 : ℝ)^4179 := by
      have hnat : (10000000008962629259 : ℕ)^1024*2500000000000000^4179 ≤ 2500000000549039^4179*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000008962629259 10000000000000000000 2500000000549039 2500000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000549039/2500000000000000 : ℝ)) (X := (10000000008962629259/10000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50266177002050001971/50000000000000000000 : ℝ) ≤ (156453412312871/156250000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (50266177002050001971/50000000000000000000 : ℝ)^1024 ≤ (156453412312871/156250000000000 : ℝ)^4179 := by
      have hnat : (50266177002050001971 : ℕ)^1024*156250000000000^4179 ≤ 156453412312871^4179*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50266177002050001971 50000000000000000000 156453412312871 156250000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156453412312871/156250000000000 : ℝ)) (X := (50266177002050001971/50000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50532353959286857647/50000000000000000000 : ℝ) ≤ (2506509193462833/2500000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (50532353959286857647/50000000000000000000 : ℝ)^1024 ≤ (2506509193462833/2500000000000000 : ℝ)^4179 := by
      have hnat : (50532353959286857647 : ℕ)^1024*2500000000000000^4179 ≤ 2506509193462833^4179*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50532353959286857647 50000000000000000000 2506509193462833 2500000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506509193462833/2500000000000000 : ℝ)) (X := (50532353959286857647/50000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8962629259/20000000000000000000 : ℝ) ≤ ((68024167308168037701/68027500000000000000 : ℝ)+2*(3254596456897/680275000000000 : ℝ)*(16/3125 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (68024167308168037701/68027500000000000000 : ℝ)+2*(3254596456897/680275000000000 : ℝ)*(16/3125 : ℝ)=(2500000000549039/2500000000000000 : ℝ) by norm_num, show 1+2*(8962629259/20000000000000000000 : ℝ)=(10000000008962629259/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(532353959286857647/100000000000000000000 : ℝ)+(8962629259/20000000000000000000 : ℝ) ≤ ((68024167308168037701/68027500000000000000 : ℝ)+(3254596456897/680275000000000 : ℝ)*((27723/100000 : ℝ)+(16/3125 : ℝ)))^(4179/1024 : ℝ) := by
    rw [show (68024167308168037701/68027500000000000000 : ℝ)+(3254596456897/680275000000000 : ℝ)*((27723/100000 : ℝ)+(16/3125 : ℝ))=(156453412312871/156250000000000 : ℝ) by norm_num, show 1+(532353959286857647/100000000000000000000 : ℝ)+(8962629259/20000000000000000000 : ℝ)=(50266177002050001971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(532353959286857647/100000000000000000000 : ℝ) ≤ ((68024167308168037701/68027500000000000000 : ℝ)+2*(3254596456897/680275000000000 : ℝ)*(27723/100000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (68024167308168037701/68027500000000000000 : ℝ)+2*(3254596456897/680275000000000 : ℝ)*(27723/100000 : ℝ)=(2506509193462833/2500000000000000 : ℝ) by norm_num, show 1+2*(532353959286857647/100000000000000000000 : ℝ)=(50532353959286857647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68024167308168037701/68027500000000000000 : ℝ)*(X 1 0+X 2 0)+(3254596456897/680275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (16/3125 : ℝ)) (hi := (27723/100000 : ℝ)) (c := (68024167308168037701/68027500000000000000 : ℝ)) (alpha := (3254596456897/680275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68024167308168037701/68027500000000000000 : ℝ)*(X 0 1+X 2 1)+(3254596456897/680275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (16/3125 : ℝ)) (hi := (27723/100000 : ℝ)) (c := (68024167308168037701/68027500000000000000 : ℝ)) (alpha := (3254596456897/680275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68024167308168037701/68027500000000000000 : ℝ)*(X 0 2+X 1 2)+(3254596456897/680275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (16/3125 : ℝ)) (hi := (27723/100000 : ℝ)) (c := (68024167308168037701/68027500000000000000 : ℝ)) (alpha := (3254596456897/680275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2087168531/10000000000 : ℝ)*X 0 0+(5695132703/10000000000 : ℝ)*X 0 1+(1001451873/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5417803561/10000000000 : ℝ)*X 1 0+(-245793153/1000000000 : ℝ)*X 1 1+(2503629203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417805677/10000000000 : ℝ)*X 2 0+(250362823/500000000 : ℝ)*X 2 1+(-2457931247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157701227/5000000000 : ℝ)*X 0 0+(460192761/1250000000 : ℝ)*X 0 1+(5056488637/10000000000 : ℝ)*X 0 2+(2157701227/5000000000 : ℝ)*X 1 0+(460192761/1250000000 : ℝ)*X 1 1+(5056488637/10000000000 : ℝ)*X 1 2+(2157701227/5000000000 : ℝ)*X 2 0+(460192761/1250000000 : ℝ)*X 2 1+(5056488637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-521986479/2500000000 : ℝ)*X 0 0+(5016565699/10000000000 : ℝ)*X 0 1+(2842820277/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241234539/10000000000 : ℝ)*X 1 0+(-1779546081/10000000000 : ℝ)*X 1 1+(5685643657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620616857/5000000000 : ℝ)*X 2 0+(568564501/1000000000 : ℝ)*X 2 1+(-1779545281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316944583/10000000000 : ℝ)*X 0 0+(125947233/250000000 : ℝ)*X 0 1+(1850253463/5000000000 : ℝ)*X 0 2+(4316944583/10000000000 : ℝ)*X 1 0+(125947233/250000000 : ℝ)*X 1 1+(1850253463/5000000000 : ℝ)*X 1 2+(4316944583/10000000000 : ℝ)*X 2 0+(125947233/250000000 : ℝ)*X 2 1+(1850253463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7203959037251676453777923097/1700687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93935933/20000000000000 : ℝ)*(base1) + (737948327/100000000000000 : ℝ)*(base19) + (1238924081/100000000000000 : ℝ)*(base23) + (371762137/100000000000000 : ℝ)*(base37) + (53344663/100000000000000 : ℝ)*(lower2) + (545263601794867/50000000000000 : ℝ)*(major0) + (545263601794867/50000000000000 : ℝ)*(major1) + (545263601794867/50000000000000 : ℝ)*(major2) + (1453755433195153/100000000000000 : ℝ)*(sp0) + (363438533701559/25000000000000 : ℝ)*(sp1) + (181719325633253/12500000000000 : ℝ)*(sp2) + (363648790275277/50000000000000 : ℝ)*(sp3) + (880474617/100000000000000 : ℝ)*(sp4) + (485617771/50000000000000 : ℝ)*(sp5) + (727298421992357/100000000000000 : ℝ)*(f.failure) + (726877921995053/50000000000000 : ℝ)*(f.sum) + (87649531284963/136055000000000000000000000000 : ℝ)*base66 + (13312482597152430767/3401375000000000000000000000000000 : ℝ)*base67 + (20803456722772805767/3401375000000000000000000000000000 : ℝ)*base69 + (15145199719500430767/3401375000000000000000000000000000 : ℝ)*base71 + (106436439699621/68027500000000000000000000000 : ℝ)*base73 + (19773516131258180767/3401375000000000000000000000000000 : ℝ)*base75 + (14783202555168680767/3401375000000000000000000000000000 : ℝ)*base77 + (22541215023180180767/3401375000000000000000000000000000 : ℝ)*base79 + (157204124849121/68027500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (37818901/10000000000000000000000 : ℝ)*base89 + (37818901/10000000000000000000000 : ℝ)*base91 + (37818901/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1388298221296314820901718963/3401375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33886547/2000000000000 : ℝ)*(base19) + (2387011073/100000000000000 : ℝ)*(base23) + (188222549/50000000000000 : ℝ)*(upper2) + (520657979/100000000000000 : ℝ)*(upper3) + (47407297/20000000000000 : ℝ)*(upper5) + (1121162876823207/100000000000000 : ℝ)*(major0) + (1121162876823207/100000000000000 : ℝ)*(major1) + (1121162876823207/100000000000000 : ℝ)*(major2) + (77632447/781250000000 : ℝ)*(sp1) + (4040370263/25000000000000 : ℝ)*(sp2) + (373648915485377/25000000000000 : ℝ)*(sp4) + (1494584030660943/100000000000000 : ℝ)*(sp5) + (186822139181173/12500000000000 : ℝ)*(sp6) + (186932519524909/25000000000000 : ℝ)*(sp7) + (186932519524909/25000000000000 : ℝ)*(f.failure) + (373648915485377/25000000000000 : ℝ)*(f.sum) + (16819947774927/17006875000000000000000000000 : ℝ)*base65 + (27040079191277372893/6802750000000000000000000000000000 : ℝ)*base68 + (15618076607156372893/6802750000000000000000000000000000 : ℝ)*base70 + (17783323040707122893/6802750000000000000000000000000000 : ℝ)*base72 + (287018018613419/136055000000000000000000000000 : ℝ)*base74 + (33778744367897622893/6802750000000000000000000000000000 : ℝ)*base76 + (3645520962106372893/6802750000000000000000000000000000 : ℝ)*base78 + (68160224481764372893/6802750000000000000000000000000000 : ℝ)*base80 + (37471094661703/17006875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1414563/2500000000000000000000 : ℝ)*base90 + (1414563/2500000000000000000000 : ℝ)*base92 + (1414563/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1166_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (16/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5783/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20329/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1166_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1166_s2_0 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069560407/5000000000 : ℝ)*x 0 + (2753147647/5000000000 : ℝ)*x 1 + (2581518893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069560407/5000000000 : ℝ)^8359 ≤ (12968451719797/100000000000000 : ℝ)^6311 := by
    have hnat : (1069560407 : ℕ)^8359*100000000000000^6311 ≤ 12968451719797^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069560407 5000000000 12968451719797 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753147647/5000000000 : ℝ)^8359 ≤ (11342403906609/25000000000000 : ℝ)^6311 := by
    have hnat : (2753147647 : ℕ)^8359*25000000000000^6311 ≤ 11342403906609^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753147647 5000000000 11342403906609 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2581518893/5000000000 : ℝ)^8359 ≤ (41661932640107/100000000000000 : ℝ)^6311 := by
    have hnat : (2581518893 : ℕ)^8359*100000000000000^6311 ≤ 41661932640107^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581518893 5000000000 41661932640107 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069560407/5000000000 : ℝ), (2753147647/5000000000 : ℝ), (2581518893/5000000000 : ℝ)] ![(12968451719797/100000000000000 : ℝ), (11342403906609/25000000000000 : ℝ), (41661932640107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069560407/5000000000 : ℝ)|^8359 ≤ (12968451719797/100000000000000 : ℝ)^6311
        have hw : |(-1069560407/5000000000 : ℝ)|=(1069560407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753147647/5000000000 : ℝ)|^8359 ≤ (11342403906609/25000000000000 : ℝ)^6311
        have hw : |(2753147647/5000000000 : ℝ)|=(2753147647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2581518893/5000000000 : ℝ)|^8359 ≤ (41661932640107/100000000000000 : ℝ)^6311
        have hw : |(2581518893/5000000000 : ℝ)|=(2581518893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s2_1 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335802363/625000000 : ℝ)*x 0 + (-579353777/2500000000 : ℝ)*x 1 + (5163040487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335802363/625000000 : ℝ)^8359 ≤ (21959447246947/50000000000000 : ℝ)^6311 := by
    have hnat : (335802363 : ℕ)^8359*50000000000000^6311 ≤ 21959447246947^6311*625000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335802363 625000000 21959447246947 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579353777/2500000000 : ℝ)^8359 ≤ (14419143977969/100000000000000 : ℝ)^6311 := by
    have hnat : (579353777 : ℕ)^8359*100000000000000^6311 ≤ 14419143977969^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579353777 2500000000 14419143977969 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5163040487/10000000000 : ℝ)^8359 ≤ (20830980753993/50000000000000 : ℝ)^6311 := by
    have hnat : (5163040487 : ℕ)^8359*50000000000000^6311 ≤ 20830980753993^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163040487 10000000000 20830980753993 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335802363/625000000 : ℝ), (-579353777/2500000000 : ℝ), (5163040487/10000000000 : ℝ)] ![(21959447246947/50000000000000 : ℝ), (14419143977969/100000000000000 : ℝ), (20830980753993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335802363/625000000 : ℝ)|^8359 ≤ (21959447246947/50000000000000 : ℝ)^6311
        have hw : |(335802363/625000000 : ℝ)|=(335802363/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-579353777/2500000000 : ℝ)|^8359 ≤ (14419143977969/100000000000000 : ℝ)^6311
        have hw : |(-579353777/2500000000 : ℝ)|=(579353777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5163040487/10000000000 : ℝ)|^8359 ≤ (20830980753993/50000000000000 : ℝ)^6311
        have hw : |(5163040487/10000000000 : ℝ)|=(5163040487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s2_2 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5372838259/10000000000 : ℝ)*x 0 + (1290759923/2500000000 : ℝ)*x 1 + (-2317415547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372838259/10000000000 : ℝ)^8359 ≤ (43918899376823/100000000000000 : ℝ)^6311 := by
    have hnat : (5372838259 : ℕ)^8359*100000000000000^6311 ≤ 43918899376823^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372838259 10000000000 43918899376823 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1290759923/2500000000 : ℝ)^8359 ≤ (20830976505573/50000000000000 : ℝ)^6311 := by
    have hnat : (1290759923 : ℕ)^8359*50000000000000^6311 ≤ 20830976505573^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290759923 2500000000 20830976505573 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2317415547/10000000000 : ℝ)^8359 ≤ (14419147595867/100000000000000 : ℝ)^6311 := by
    have hnat : (2317415547 : ℕ)^8359*100000000000000^6311 ≤ 14419147595867^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317415547 10000000000 14419147595867 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372838259/10000000000 : ℝ), (1290759923/2500000000 : ℝ), (-2317415547/10000000000 : ℝ)] ![(43918899376823/100000000000000 : ℝ), (20830976505573/50000000000000 : ℝ), (14419147595867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372838259/10000000000 : ℝ)|^8359 ≤ (43918899376823/100000000000000 : ℝ)^6311
        have hw : |(5372838259/10000000000 : ℝ)|=(5372838259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1290759923/2500000000 : ℝ)|^8359 ≤ (20830976505573/50000000000000 : ℝ)^6311
        have hw : |(1290759923/2500000000 : ℝ)|=(1290759923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2317415547/10000000000 : ℝ)|^8359 ≤ (14419147595867/100000000000000 : ℝ)^6311
        have hw : |(-2317415547/10000000000 : ℝ)|=(2317415547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s2_3 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351101289/10000000000 : ℝ)*x 0 + (4021373137/10000000000 : ℝ)*x 1 + (188299461/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351101289/10000000000 : ℝ)^8359 ≤ (16606955657197/50000000000000 : ℝ)^6311 := by
    have hnat : (4351101289 : ℕ)^8359*50000000000000^6311 ≤ 16606955657197^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351101289 10000000000 16606955657197 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4021373137/10000000000 : ℝ)^8359 ≤ (7480468847017/25000000000000 : ℝ)^6311 := by
    have hnat : (4021373137 : ℕ)^8359*25000000000000^6311 ≤ 7480468847017^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021373137 10000000000 7480468847017 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188299461/400000000 : ℝ)^8359 ≤ (9216053320127/25000000000000 : ℝ)^6311 := by
    have hnat : (188299461 : ℕ)^8359*25000000000000^6311 ≤ 9216053320127^6311*400000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188299461 400000000 9216053320127 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351101289/10000000000 : ℝ), (4021373137/10000000000 : ℝ), (188299461/400000000 : ℝ)] ![(16606955657197/50000000000000 : ℝ), (7480468847017/25000000000000 : ℝ), (9216053320127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351101289/10000000000 : ℝ)|^8359 ≤ (16606955657197/50000000000000 : ℝ)^6311
        have hw : |(4351101289/10000000000 : ℝ)|=(4351101289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4021373137/10000000000 : ℝ)|^8359 ≤ (7480468847017/25000000000000 : ℝ)^6311
        have hw : |(4021373137/10000000000 : ℝ)|=(4021373137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188299461/400000000 : ℝ)|^8359 ≤ (9216053320127/25000000000000 : ℝ)^6311
        have hw : |(188299461/400000000 : ℝ)|=(188299461/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s2_4 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139216333/10000000000 : ℝ)*x 0 + (5165365859/10000000000 : ℝ)*x 1 + (2751972367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139216333/10000000000 : ℝ)^8359 ≤ (405288085353/3125000000000 : ℝ)^6311 := by
    have hnat : (2139216333 : ℕ)^8359*3125000000000^6311 ≤ 405288085353^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139216333 10000000000 405288085353 3125000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5165365859/10000000000 : ℝ)^8359 ≤ (41686816549889/100000000000000 : ℝ)^6311 := by
    have hnat : (5165365859 : ℕ)^8359*100000000000000^6311 ≤ 41686816549889^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165365859 10000000000 41686816549889 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751972367/5000000000 : ℝ)^8359 ≤ (11335991175773/25000000000000 : ℝ)^6311 := by
    have hnat : (2751972367 : ℕ)^8359*25000000000000^6311 ≤ 11335991175773^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751972367 5000000000 11335991175773 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139216333/10000000000 : ℝ), (5165365859/10000000000 : ℝ), (2751972367/5000000000 : ℝ)] ![(405288085353/3125000000000 : ℝ), (41686816549889/100000000000000 : ℝ), (11335991175773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139216333/10000000000 : ℝ)|^8359 ≤ (405288085353/3125000000000 : ℝ)^6311
        have hw : |(-2139216333/10000000000 : ℝ)|=(2139216333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5165365859/10000000000 : ℝ)|^8359 ≤ (41686816549889/100000000000000 : ℝ)^6311
        have hw : |(5165365859/10000000000 : ℝ)|=(5165365859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751972367/5000000000 : ℝ)|^8359 ≤ (11335991175773/25000000000000 : ℝ)^6311
        have hw : |(2751972367/5000000000 : ℝ)|=(2751972367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s2_5 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285605833/10000000000 : ℝ)*x 0 + (-988254863/5000000000 : ℝ)*x 1 + (5503944729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285605833/10000000000 : ℝ)^8359 ≤ (42976940475141/100000000000000 : ℝ)^6311 := by
    have hnat : (5285605833 : ℕ)^8359*100000000000000^6311 ≤ 42976940475141^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285605833 10000000000 42976940475141 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (988254863/5000000000 : ℝ)^8359 ≤ (11679094856129/100000000000000 : ℝ)^6311 := by
    have hnat : (988254863 : ℕ)^8359*100000000000000^6311 ≤ 11679094856129^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988254863 5000000000 11679094856129 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5503944729/10000000000 : ℝ)^8359 ≤ (11335991162133/25000000000000 : ℝ)^6311 := by
    have hnat : (5503944729 : ℕ)^8359*25000000000000^6311 ≤ 11335991162133^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503944729 10000000000 11335991162133 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285605833/10000000000 : ℝ), (-988254863/5000000000 : ℝ), (5503944729/10000000000 : ℝ)] ![(42976940475141/100000000000000 : ℝ), (11679094856129/100000000000000 : ℝ), (11335991162133/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285605833/10000000000 : ℝ)|^8359 ≤ (42976940475141/100000000000000 : ℝ)^6311
        have hw : |(5285605833/10000000000 : ℝ)|=(5285605833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-988254863/5000000000 : ℝ)|^8359 ≤ (11679094856129/100000000000000 : ℝ)^6311
        have hw : |(-988254863/5000000000 : ℝ)|=(988254863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5503944729/10000000000 : ℝ)|^8359 ≤ (11335991162133/25000000000000 : ℝ)^6311
        have hw : |(5503944729/10000000000 : ℝ)|=(5503944729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s2_6 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642802979/5000000000 : ℝ)*x 0 + (220157789/400000000 : ℝ)*x 1 + (-49412739/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642802979/5000000000 : ℝ)^8359 ≤ (42976941821333/100000000000000 : ℝ)^6311 := by
    have hnat : (2642802979 : ℕ)^8359*100000000000000^6311 ≤ 42976941821333^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642802979 5000000000 42976941821333 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220157789/400000000 : ℝ)^8359 ≤ (11335991151221/25000000000000 : ℝ)^6311 := by
    have hnat : (220157789 : ℕ)^8359*25000000000000^6311 ≤ 11335991151221^6311*400000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220157789 400000000 11335991151221 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49412739/250000000 : ℝ)^8359 ≤ (5839546778467/50000000000000 : ℝ)^6311 := by
    have hnat : (49412739 : ℕ)^8359*50000000000000^6311 ≤ 5839546778467^6311*250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49412739 250000000 5839546778467 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642802979/5000000000 : ℝ), (220157789/400000000 : ℝ), (-49412739/250000000 : ℝ)] ![(42976941821333/100000000000000 : ℝ), (11335991151221/25000000000000 : ℝ), (5839546778467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642802979/5000000000 : ℝ)|^8359 ≤ (42976941821333/100000000000000 : ℝ)^6311
        have hw : |(2642802979/5000000000 : ℝ)|=(2642802979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220157789/400000000 : ℝ)|^8359 ≤ (11335991151221/25000000000000 : ℝ)^6311
        have hw : |(220157789/400000000 : ℝ)|=(220157789/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49412739/250000000 : ℝ)|^8359 ≤ (5839546778467/50000000000000 : ℝ)^6311
        have hw : |(-49412739/250000000 : ℝ)|=(49412739/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s2_7 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087823457/2500000000 : ℝ)*x 0 + (293927219/625000000 : ℝ)*x 1 + (2013034451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087823457/2500000000 : ℝ)^8359 ≤ (4151982251673/12500000000000 : ℝ)^6311 := by
    have hnat : (1087823457 : ℕ)^8359*12500000000000^6311 ≤ 4151982251673^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087823457 2500000000 4151982251673 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293927219/625000000 : ℝ)^8359 ≤ (4601997446047/12500000000000 : ℝ)^6311 := by
    have hnat : (293927219 : ℕ)^8359*12500000000000^6311 ≤ 4601997446047^6311*625000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293927219 625000000 4601997446047 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013034451/5000000000 : ℝ)^8359 ≤ (14984081202471/50000000000000 : ℝ)^6311 := by
    have hnat : (2013034451 : ℕ)^8359*50000000000000^6311 ≤ 14984081202471^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013034451 5000000000 14984081202471 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087823457/2500000000 : ℝ), (293927219/625000000 : ℝ), (2013034451/5000000000 : ℝ)] ![(4151982251673/12500000000000 : ℝ), (4601997446047/12500000000000 : ℝ), (14984081202471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087823457/2500000000 : ℝ)|^8359 ≤ (4151982251673/12500000000000 : ℝ)^6311
        have hw : |(1087823457/2500000000 : ℝ)|=(1087823457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(293927219/625000000 : ℝ)|^8359 ≤ (4601997446047/12500000000000 : ℝ)^6311
        have hw : |(293927219/625000000 : ℝ)|=(293927219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013034451/5000000000 : ℝ)|^8359 ≤ (14984081202471/50000000000000 : ℝ)^6311
        have hw : |(2013034451/5000000000 : ℝ)|=(2013034451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1166_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5783/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4589/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1027/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20329/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5783/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20329/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5783/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20329/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5783/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20329/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5783/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20329/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5783/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20329/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5783/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5783/100000 : ℝ) ^ (4179/1024 : ℝ) ≤ (177545422076681/20000000000000000000 : ℝ) := by
    have hpowers : (5783/100000 : ℝ)^4179 ≤ (177545422076681/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5783 : ℕ)^4179*20000000000000000000^1024 ≤ 177545422076681^1024*100000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5783 100000 177545422076681 20000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5783/100000 : ℝ)) (X := (177545422076681/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20329/100000 : ℝ) ^ (4179/1024 : ℝ) ≤ (37525253261007821/25000000000000000000 : ℝ) := by
    have hpowers : (20329/100000 : ℝ)^4179 ≤ (37525253261007821/25000000000000000000 : ℝ)^1024 := by
      have hnat : (20329 : ℕ)^4179*25000000000000000000^1024 ≤ 37525253261007821^1024*100000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20329 100000 37525253261007821 25000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20329/100000 : ℝ)) (X := (37525253261007821/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000177545422076681/10000000000000000000 : ℝ) ≤ (2500010876124297/2500000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (10000177545422076681/10000000000000000000 : ℝ)^1024 ≤ (2500010876124297/2500000000000000 : ℝ)^4179 := by
      have hnat : (10000177545422076681 : ℕ)^1024*2500000000000000^4179 ≤ 2500010876124297^4179*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000177545422076681 10000000000000000000 2500010876124297 2500000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500010876124297/2500000000000000 : ℝ)) (X := (10000177545422076681/10000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100150988740154414689/100000000000000000000 : ℝ) ≤ (10003697641189797/10000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (100150988740154414689/100000000000000000000 : ℝ)^1024 ≤ (10003697641189797/10000000000000000 : ℝ)^4179 := by
      have hnat : (100150988740154414689 : ℕ)^1024*10000000000000000^4179 ≤ 10003697641189797^4179*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100150988740154414689 100000000000000000000 10003697641189797 10000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003697641189797/10000000000000000 : ℝ)) (X := (100150988740154414689/100000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12537525253261007821/12500000000000000000 : ℝ) ≤ (5003675888941203/5000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (12537525253261007821/12500000000000000000 : ℝ)^1024 ≤ (5003675888941203/5000000000000000 : ℝ)^4179 := by
      have hnat : (12537525253261007821 : ℕ)^1024*5000000000000000^4179 ≤ 5003675888941203^4179*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12537525253261007821 12500000000000000000 5003675888941203 5000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003675888941203/5000000000000000 : ℝ)) (X := (12537525253261007821/12500000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(177545422076681/20000000000000000000 : ℝ) ≤ ((72709184535714690477/72730000000000000000 : ℝ)+2*(3654136692609/1454600000000000 : ℝ)*(5783/100000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (72709184535714690477/72730000000000000000 : ℝ)+2*(3654136692609/1454600000000000 : ℝ)*(5783/100000 : ℝ)=(2500010876124297/2500000000000000 : ℝ) by norm_num, show 1+2*(177545422076681/20000000000000000000 : ℝ)=(10000177545422076681/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37525253261007821/25000000000000000000 : ℝ)+(177545422076681/20000000000000000000 : ℝ) ≤ ((72709184535714690477/72730000000000000000 : ℝ)+(3654136692609/1454600000000000 : ℝ)*((20329/100000 : ℝ)+(5783/100000 : ℝ)))^(4179/1024 : ℝ) := by
    rw [show (72709184535714690477/72730000000000000000 : ℝ)+(3654136692609/1454600000000000 : ℝ)*((20329/100000 : ℝ)+(5783/100000 : ℝ))=(10003697641189797/10000000000000000 : ℝ) by norm_num, show 1+(37525253261007821/25000000000000000000 : ℝ)+(177545422076681/20000000000000000000 : ℝ)=(100150988740154414689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37525253261007821/25000000000000000000 : ℝ) ≤ ((72709184535714690477/72730000000000000000 : ℝ)+2*(3654136692609/1454600000000000 : ℝ)*(20329/100000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (72709184535714690477/72730000000000000000 : ℝ)+2*(3654136692609/1454600000000000 : ℝ)*(20329/100000 : ℝ)=(5003675888941203/5000000000000000 : ℝ) by norm_num, show 1+2*(37525253261007821/25000000000000000000 : ℝ)=(12537525253261007821/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72709184535714690477/72730000000000000000 : ℝ)*(X 1 0+X 2 0)+(3654136692609/1454600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (5783/100000 : ℝ)) (hi := (20329/100000 : ℝ)) (c := (72709184535714690477/72730000000000000000 : ℝ)) (alpha := (3654136692609/1454600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72709184535714690477/72730000000000000000 : ℝ)*(X 0 1+X 2 1)+(3654136692609/1454600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (5783/100000 : ℝ)) (hi := (20329/100000 : ℝ)) (c := (72709184535714690477/72730000000000000000 : ℝ)) (alpha := (3654136692609/1454600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72709184535714690477/72730000000000000000 : ℝ)*(X 0 2+X 1 2)+(3654136692609/1454600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (5783/100000 : ℝ)) (hi := (20329/100000 : ℝ)) (c := (72709184535714690477/72730000000000000000 : ℝ)) (alpha := (3654136692609/1454600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1069560407/5000000000 : ℝ)*X 0 0+(2753147647/5000000000 : ℝ)*X 0 1+(2581518893/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335802363/625000000 : ℝ)*X 1 0+(-579353777/2500000000 : ℝ)*X 1 1+(5163040487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372838259/10000000000 : ℝ)*X 2 0+(1290759923/2500000000 : ℝ)*X 2 1+(-2317415547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351101289/10000000000 : ℝ)*X 0 0+(4021373137/10000000000 : ℝ)*X 0 1+(188299461/400000000 : ℝ)*X 0 2+(4351101289/10000000000 : ℝ)*X 1 0+(4021373137/10000000000 : ℝ)*X 1 1+(188299461/400000000 : ℝ)*X 1 2+(4351101289/10000000000 : ℝ)*X 2 0+(4021373137/10000000000 : ℝ)*X 2 1+(188299461/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2139216333/10000000000 : ℝ)*X 0 0+(5165365859/10000000000 : ℝ)*X 0 1+(2751972367/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5285605833/10000000000 : ℝ)*X 1 0+(-988254863/5000000000 : ℝ)*X 1 1+(5503944729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2642802979/5000000000 : ℝ)*X 2 0+(220157789/400000000 : ℝ)*X 2 1+(-49412739/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087823457/2500000000 : ℝ)*X 0 0+(293927219/625000000 : ℝ)*X 0 1+(2013034451/5000000000 : ℝ)*X 0 2+(1087823457/2500000000 : ℝ)*X 1 0+(293927219/625000000 : ℝ)*X 1 1+(2013034451/5000000000 : ℝ)*X 1 2+(1087823457/2500000000 : ℝ)*X 2 0+(293927219/625000000 : ℝ)*X 2 1+(2013034451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34053844928229483921531/14546000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25989799/12500000000000 : ℝ)*(base15) + (62111927/50000000000000 : ℝ)*(upper2) + (20800533/12500000000000 : ℝ)*(upper3) + (138309279/100000000000000 : ℝ)*(upper4) + (87415801490209/4000000000000 : ℝ)*(major0) + (87415801490209/4000000000000 : ℝ)*(major1) + (87415801490209/4000000000000 : ℝ)*(major2) + (1456641615808173/50000000000000 : ℝ)*(sp0) + (11653192302247/400000000000 : ℝ)*(sp1) + (364161983122773/12500000000000 : ℝ)*(sp2) + (728743910274023/50000000000000 : ℝ)*(sp3) + (3762965949/25000000000000 : ℝ)*(sp4) + (2418497957/100000000000000 : ℝ)*(sp6) + (973111281/25000000000000 : ℝ)*(sp7) + (145749171299317/10000000000000 : ℝ)*(f.failure) + (1456649141740071/50000000000000 : ℝ)*(f.sum) + (26696754388279/14546000000000000000000000000 : ℝ)*base66 + (688650435038030307/290920000000000000000000000000000 : ℝ)*base68 + (858220410255470307/290920000000000000000000000000000 : ℝ)*base70 + (2116740383536369693/290920000000000000000000000000000 : ℝ)*base71 + (33769752380697/14546000000000000000000000000 : ℝ)*base73 + (679558301223070307/290920000000000000000000000000000 : ℝ)*base76 + (301410795011329693/290920000000000000000000000000000 : ℝ)*base77 + (24552261060169693/290920000000000000000000000000000 : ℝ)*base79 + (46355982333/116368000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (382181/1000000000000000000000 : ℝ)*base89 + (382181/1000000000000000000000 : ℝ)*base91 + (382181/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (876079357329082647680215527/129875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394067857/25000000000000 : ℝ)*(base19) + (422422163/25000000000000 : ℝ)*(base23) + (188065159/100000000000000 : ℝ)*(upper3) + (3196849/100000000000000 : ℝ)*(lower4) + (145472501/100000000000000 : ℝ)*(upper5) + (553892018822827/25000000000000 : ℝ)*(major0) + (553892018822827/25000000000000 : ℝ)*(major1) + (553892018822827/25000000000000 : ℝ)*(major2) + (15228863819/100000000000000 : ℝ)*(sp1) + (17502280367/100000000000000 : ℝ)*(sp2) + (738380274750301/25000000000000 : ℝ)*(sp4) + (1476752146932979/50000000000000 : ℝ)*(sp5) + (1476750953516093/50000000000000 : ℝ)*(sp6) + (1477614826729463/100000000000000 : ℝ)*(sp7) + (1477614826729463/100000000000000 : ℝ)*(f.failure) + (738380274750301/25000000000000 : ℝ)*(f.sum) + (48248517961697/18182500000000000000000000000 : ℝ)*base66 + (24467442448358268479/1818250000000000000000000000000000 : ℝ)*base67 + (13465083013532768479/1818250000000000000000000000000000 : ℝ)*base69 + (2831344685116768479/1818250000000000000000000000000000 : ℝ)*base71 + (121710946915603/18182500000000000000000000000 : ℝ)*base73 + (21360623632476018479/1818250000000000000000000000000000 : ℝ)*base75 + (8922257676698018479/1818250000000000000000000000000000 : ℝ)*base77 + (10409185141659768479/1818250000000000000000000000000000 : ℝ)*base79 + (53984742022581/36365000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (100067641/10000000000000000000000 : ℝ)*base90 + (100067641/10000000000000000000000 : ℝ)*base92 + (100067641/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1166_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20329/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5783/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4589/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1027/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1166_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1166_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4589/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1027/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1166_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1166_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1166_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4589/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1027/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1166_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
