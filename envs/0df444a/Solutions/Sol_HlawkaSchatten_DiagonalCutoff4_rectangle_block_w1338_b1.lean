-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1338_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:28.775461+00:00
-- url     : https://prove2.me/submissions/e8bd6eba-096b-4b7d-bca0-03f7a8e13b4c

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
theorem support_rectangle_w1338_s3_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2045631147/10000000000 : ℝ)*x 0 + (5427687029/10000000000 : ℝ)*x 1 + (209235733/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2045631147/10000000000 : ℝ)^2149 ≤ (6226538611829/50000000000000 : ℝ)^1637 := by
    have hnat : (2045631147 : ℕ)^2149*50000000000000^1637 ≤ 6226538611829^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045631147 10000000000 6226538611829 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427687029/10000000000 : ℝ)^2149 ≤ (44834362153321/100000000000000 : ℝ)^1637 := by
    have hnat : (5427687029 : ℕ)^2149*100000000000000^1637 ≤ 44834362153321^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427687029 10000000000 44834362153321 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209235733/400000000 : ℝ)^2149 ≤ (21356280307833/50000000000000 : ℝ)^1637 := by
    have hnat : (209235733 : ℕ)^2149*50000000000000^1637 ≤ 21356280307833^1637*400000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209235733 400000000 21356280307833 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2045631147/10000000000 : ℝ), (5427687029/10000000000 : ℝ), (209235733/400000000 : ℝ)] ![(6226538611829/50000000000000 : ℝ), (44834362153321/100000000000000 : ℝ), (21356280307833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2045631147/10000000000 : ℝ)|^2149 ≤ (6226538611829/50000000000000 : ℝ)^1637
        have hw : |(-2045631147/10000000000 : ℝ)|=(2045631147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427687029/10000000000 : ℝ)|^2149 ≤ (44834362153321/100000000000000 : ℝ)^1637
        have hw : |(5427687029/10000000000 : ℝ)|=(5427687029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209235733/400000000 : ℝ)|^2149 ≤ (21356280307833/50000000000000 : ℝ)^1637
        have hw : |(209235733/400000000 : ℝ)|=(209235733/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s3_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33455197/62500000 : ℝ)*x 0 + (-2146217563/10000000000 : ℝ)*x 1 + (2615446699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33455197/62500000 : ℝ)^2149 ≤ (5503049460181/12500000000000 : ℝ)^1637 := by
    have hnat : (33455197 : ℕ)^2149*12500000000000^1637 ≤ 5503049460181^1637*62500000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33455197 62500000 5503049460181 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146217563/10000000000 : ℝ)^2149 ≤ (13263042908119/100000000000000 : ℝ)^1637 := by
    have hnat : (2146217563 : ℕ)^2149*100000000000000^1637 ≤ 13263042908119^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146217563 10000000000 13263042908119 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615446699/5000000000 : ℝ)^2149 ≤ (1334767543693/3125000000000 : ℝ)^1637 := by
    have hnat : (2615446699 : ℕ)^2149*3125000000000^1637 ≤ 1334767543693^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615446699 5000000000 1334767543693 3125000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33455197/62500000 : ℝ), (-2146217563/10000000000 : ℝ), (2615446699/5000000000 : ℝ)] ![(5503049460181/12500000000000 : ℝ), (13263042908119/100000000000000 : ℝ), (1334767543693/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33455197/62500000 : ℝ)|^2149 ≤ (5503049460181/12500000000000 : ℝ)^1637
        have hw : |(33455197/62500000 : ℝ)|=(33455197/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146217563/10000000000 : ℝ)|^2149 ≤ (13263042908119/100000000000000 : ℝ)^1637
        have hw : |(-2146217563/10000000000 : ℝ)|=(2146217563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615446699/5000000000 : ℝ)|^2149 ≤ (1334767543693/3125000000000 : ℝ)^1637
        have hw : |(2615446699/5000000000 : ℝ)|=(2615446699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s3_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53528313/100000000 : ℝ)*x 0 + (1046178733/2000000000 : ℝ)*x 1 + (-1073108751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53528313/100000000 : ℝ)^2149 ≤ (22012196653069/50000000000000 : ℝ)^1637 := by
    have hnat : (53528313 : ℕ)^2149*50000000000000^1637 ≤ 22012196653069^1637*100000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53528313 100000000 22012196653069 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046178733/2000000000 : ℝ)^2149 ≤ (10678141065059/25000000000000 : ℝ)^1637 := by
    have hnat : (1046178733 : ℕ)^2149*25000000000000^1637 ≤ 10678141065059^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046178733 2000000000 10678141065059 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073108751/5000000000 : ℝ)^2149 ≤ (6631521206627/50000000000000 : ℝ)^1637 := by
    have hnat : (1073108751 : ℕ)^2149*50000000000000^1637 ≤ 6631521206627^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073108751 5000000000 6631521206627 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53528313/100000000 : ℝ), (1046178733/2000000000 : ℝ), (-1073108751/5000000000 : ℝ)] ![(22012196653069/50000000000000 : ℝ), (10678141065059/25000000000000 : ℝ), (6631521206627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53528313/100000000 : ℝ)|^2149 ≤ (22012196653069/50000000000000 : ℝ)^1637
        have hw : |(53528313/100000000 : ℝ)|=(53528313/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046178733/2000000000 : ℝ)|^2149 ≤ (10678141065059/25000000000000 : ℝ)^1637
        have hw : |(1046178733/2000000000 : ℝ)|=(1046178733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073108751/5000000000 : ℝ)|^2149 ≤ (6631521206627/50000000000000 : ℝ)^1637
        have hw : |(-1073108751/5000000000 : ℝ)|=(1073108751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s3_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081644167/2500000000 : ℝ)*x 0 + (515670911/1250000000 : ℝ)*x 1 + (283559089/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081644167/2500000000 : ℝ)^2149 ≤ (33292184068561/100000000000000 : ℝ)^1637 := by
    have hnat : (1081644167 : ℕ)^2149*100000000000000^1637 ≤ 33292184068561^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081644167 2500000000 33292184068561 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515670911/1250000000 : ℝ)^2149 ≤ (15637305590783/50000000000000 : ℝ)^1637 := by
    have hnat : (515670911 : ℕ)^2149*50000000000000^1637 ≤ 15637305590783^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515670911 1250000000 15637305590783 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283559089/625000000 : ℝ)^2149 ≤ (35433204735459/100000000000000 : ℝ)^1637 := by
    have hnat : (283559089 : ℕ)^2149*100000000000000^1637 ≤ 35433204735459^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283559089 625000000 35433204735459 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081644167/2500000000 : ℝ), (515670911/1250000000 : ℝ), (283559089/625000000 : ℝ)] ![(33292184068561/100000000000000 : ℝ), (15637305590783/50000000000000 : ℝ), (35433204735459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081644167/2500000000 : ℝ)|^2149 ≤ (33292184068561/100000000000000 : ℝ)^1637
        have hw : |(1081644167/2500000000 : ℝ)|=(1081644167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515670911/1250000000 : ℝ)|^2149 ≤ (15637305590783/50000000000000 : ℝ)^1637
        have hw : |(515670911/1250000000 : ℝ)|=(515670911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283559089/625000000 : ℝ)|^2149 ≤ (35433204735459/100000000000000 : ℝ)^1637
        have hw : |(283559089/625000000 : ℝ)|=(283559089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s3_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-204565059/1000000000 : ℝ)*x 0 + (5231715539/10000000000 : ℝ)*x 1 + (339178743/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204565059/1000000000 : ℝ)^2149 ≤ (6226616302883/50000000000000 : ℝ)^1637 := by
    have hnat : (204565059 : ℕ)^2149*50000000000000^1637 ≤ 6226616302883^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204565059 1000000000 6226616302883 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231715539/10000000000 : ℝ)^2149 ≤ (5340171801531/12500000000000 : ℝ)^1637 := by
    have hnat : (5231715539 : ℕ)^2149*12500000000000^1637 ≤ 5340171801531^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231715539 10000000000 5340171801531 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339178743/625000000 : ℝ)^2149 ≤ (1400793530163/3125000000000 : ℝ)^1637 := by
    have hnat : (339178743 : ℕ)^2149*3125000000000^1637 ≤ 1400793530163^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339178743 625000000 1400793530163 3125000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204565059/1000000000 : ℝ), (5231715539/10000000000 : ℝ), (339178743/625000000 : ℝ)] ![(6226616302883/50000000000000 : ℝ), (5340171801531/12500000000000 : ℝ), (1400793530163/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204565059/1000000000 : ℝ)|^2149 ≤ (6226616302883/50000000000000 : ℝ)^1637
        have hw : |(-204565059/1000000000 : ℝ)|=(204565059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231715539/10000000000 : ℝ)|^2149 ≤ (5340171801531/12500000000000 : ℝ)^1637
        have hw : |(5231715539/10000000000 : ℝ)|=(5231715539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339178743/625000000 : ℝ)|^2149 ≤ (1400793530163/3125000000000 : ℝ)^1637
        have hw : |(339178743/625000000 : ℝ)|=(339178743/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s3_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302163643/10000000000 : ℝ)*x 0 + (-1950251107/10000000000 : ℝ)*x 1 + (2713430089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302163643/10000000000 : ℝ)^2149 ≤ (43478153137067/100000000000000 : ℝ)^1637 := by
    have hnat : (5302163643 : ℕ)^2149*100000000000000^1637 ≤ 43478153137067^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302163643 10000000000 43478153137067 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1950251107/10000000000 : ℝ)^2149 ≤ (11696450744341/100000000000000 : ℝ)^1637 := by
    have hnat : (1950251107 : ℕ)^2149*100000000000000^1637 ≤ 11696450744341^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950251107 10000000000 11696450744341 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713430089/5000000000 : ℝ)^2149 ≤ (22412698054893/50000000000000 : ℝ)^1637 := by
    have hnat : (2713430089 : ℕ)^2149*50000000000000^1637 ≤ 22412698054893^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713430089 5000000000 22412698054893 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302163643/10000000000 : ℝ), (-1950251107/10000000000 : ℝ), (2713430089/5000000000 : ℝ)] ![(43478153137067/100000000000000 : ℝ), (11696450744341/100000000000000 : ℝ), (22412698054893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302163643/10000000000 : ℝ)|^2149 ≤ (43478153137067/100000000000000 : ℝ)^1637
        have hw : |(5302163643/10000000000 : ℝ)|=(5302163643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1950251107/10000000000 : ℝ)|^2149 ≤ (11696450744341/100000000000000 : ℝ)^1637
        have hw : |(-1950251107/10000000000 : ℝ)|=(1950251107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713430089/5000000000 : ℝ)|^2149 ≤ (22412698054893/50000000000000 : ℝ)^1637
        have hw : |(2713430089/5000000000 : ℝ)|=(2713430089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s3_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302164519/10000000000 : ℝ)*x 0 + (2713429807/5000000000 : ℝ)*x 1 + (-975125343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302164519/10000000000 : ℝ)^2149 ≤ (21739081283513/50000000000000 : ℝ)^1637 := by
    have hnat : (5302164519 : ℕ)^2149*50000000000000^1637 ≤ 21739081283513^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302164519 10000000000 21739081283513 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713429807/5000000000 : ℝ)^2149 ≤ (2241269499707/5000000000000 : ℝ)^1637 := by
    have hnat : (2713429807 : ℕ)^2149*5000000000000^1637 ≤ 2241269499707^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713429807 5000000000 2241269499707 5000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975125343/5000000000 : ℝ)^2149 ≤ (2924111857431/25000000000000 : ℝ)^1637 := by
    have hnat : (975125343 : ℕ)^2149*25000000000000^1637 ≤ 2924111857431^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975125343 5000000000 2924111857431 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302164519/10000000000 : ℝ), (2713429807/5000000000 : ℝ), (-975125343/5000000000 : ℝ)] ![(21739081283513/50000000000000 : ℝ), (2241269499707/5000000000000 : ℝ), (2924111857431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302164519/10000000000 : ℝ)|^2149 ≤ (21739081283513/50000000000000 : ℝ)^1637
        have hw : |(5302164519/10000000000 : ℝ)|=(5302164519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713429807/5000000000 : ℝ)|^2149 ≤ (2241269499707/5000000000000 : ℝ)^1637
        have hw : |(2713429807/5000000000 : ℝ)|=(2713429807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-975125343/5000000000 : ℝ)|^2149 ≤ (2924111857431/25000000000000 : ℝ)^1637
        have hw : |(-975125343/5000000000 : ℝ)|=(975125343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s3_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2163309123/5000000000 : ℝ)*x 0 + (4535225719/10000000000 : ℝ)*x 1 + (1031774123/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163309123/5000000000 : ℝ)^2149 ≤ (16646302034559/50000000000000 : ℝ)^1637 := by
    have hnat : (2163309123 : ℕ)^2149*50000000000000^1637 ≤ 16646302034559^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163309123 5000000000 16646302034559 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535225719/10000000000 : ℝ)^2149 ≤ (35415574308809/100000000000000 : ℝ)^1637 := by
    have hnat : (4535225719 : ℕ)^2149*100000000000000^1637 ≤ 35415574308809^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535225719 10000000000 35415574308809 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031774123/2500000000 : ℝ)^2149 ≤ (977869425373/3125000000000 : ℝ)^1637 := by
    have hnat : (1031774123 : ℕ)^2149*3125000000000^1637 ≤ 977869425373^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031774123 2500000000 977869425373 3125000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163309123/5000000000 : ℝ), (4535225719/10000000000 : ℝ), (1031774123/2500000000 : ℝ)] ![(16646302034559/50000000000000 : ℝ), (35415574308809/100000000000000 : ℝ), (977869425373/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163309123/5000000000 : ℝ)|^2149 ≤ (16646302034559/50000000000000 : ℝ)^1637
        have hw : |(2163309123/5000000000 : ℝ)|=(2163309123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535225719/10000000000 : ℝ)|^2149 ≤ (35415574308809/100000000000000 : ℝ)^1637
        have hw : |(4535225719/10000000000 : ℝ)|=(4535225719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031774123/2500000000 : ℝ)|^2149 ≤ (977869425373/3125000000000 : ℝ)^1637
        have hw : |(1031774123/2500000000 : ℝ)|=(1031774123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (403/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (10849/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15013/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (403/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (393/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (403/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (393/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (403/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (393/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (403/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (393/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (403/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (393/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (403/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (393/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (393/4000 : ℝ) ^ (4297/1024 : ℝ) ≤ (590930136525971/10000000000000000000 : ℝ) := by
    have hpowers : (393/4000 : ℝ)^4297 ≤ (590930136525971/10000000000000000000 : ℝ)^1024 := by
      have hnat : (393 : ℕ)^4297*10000000000000000000^1024 ≤ 590930136525971^1024*4000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        393 4000 590930136525971 10000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (393/4000 : ℝ)) (X := (590930136525971/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (403/2500 : ℝ) ^ (4297/1024 : ℝ) ≤ (47192672960106519/100000000000000000000 : ℝ) := by
    have hpowers : (403/2500 : ℝ)^4297 ≤ (47192672960106519/100000000000000000000 : ℝ)^1024 := by
      have hnat : (403 : ℕ)^4297*100000000000000000000^1024 ≤ 47192672960106519^1024*2500^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        403 2500 47192672960106519 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (403/2500 : ℝ)) (X := (47192672960106519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000590930136525971/5000000000000000000 : ℝ) ≤ (2500070407868873/2500000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (5000590930136525971/5000000000000000000 : ℝ)^1024 ≤ (2500070407868873/2500000000000000 : ℝ)^4297 := by
      have hnat : (5000590930136525971 : ℕ)^1024*2500000000000000^4297 ≤ 2500070407868873^4297*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000590930136525971 5000000000000000000 2500070407868873 2500000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070407868873/2500000000000000 : ℝ)) (X := (5000590930136525971/5000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053101974325366229/100000000000000000000 : ℝ) ≤ (10001265194977769/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (100053101974325366229/100000000000000000000 : ℝ)^1024 ≤ (10001265194977769/10000000000000000 : ℝ)^4297 := by
      have hnat : (100053101974325366229 : ℕ)^1024*10000000000000000^4297 ≤ 10001265194977769^4297*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053101974325366229 100000000000000000000 10001265194977769 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001265194977769/10000000000000000 : ℝ)) (X := (100053101974325366229/100000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047192672960106519/50000000000000000000 : ℝ) ≤ (5001124379240023/5000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50047192672960106519/50000000000000000000 : ℝ)^1024 ≤ (5001124379240023/5000000000000000 : ℝ)^4297 := by
      have hnat : (50047192672960106519 : ℕ)^1024*5000000000000000^4297 ≤ 5001124379240023^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047192672960106519 50000000000000000000 5001124379240023 5000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001124379240023/5000000000000000 : ℝ)) (X := (50047192672960106519/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(590930136525971/10000000000000000000 : ℝ) ≤ ((6293244584731847909/6295000000000000000 : ℝ)+2*(983563502277/629500000000000 : ℝ)*(393/4000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (6293244584731847909/6295000000000000000 : ℝ)+2*(983563502277/629500000000000 : ℝ)*(393/4000 : ℝ)=(2500070407868873/2500000000000000 : ℝ) by norm_num, show 1+2*(590930136525971/10000000000000000000 : ℝ)=(5000590930136525971/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47192672960106519/100000000000000000000 : ℝ)+(590930136525971/10000000000000000000 : ℝ) ≤ ((6293244584731847909/6295000000000000000 : ℝ)+(983563502277/629500000000000 : ℝ)*((403/2500 : ℝ)+(393/4000 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (6293244584731847909/6295000000000000000 : ℝ)+(983563502277/629500000000000 : ℝ)*((403/2500 : ℝ)+(393/4000 : ℝ))=(10001265194977769/10000000000000000 : ℝ) by norm_num, show 1+(47192672960106519/100000000000000000000 : ℝ)+(590930136525971/10000000000000000000 : ℝ)=(100053101974325366229/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47192672960106519/100000000000000000000 : ℝ) ≤ ((6293244584731847909/6295000000000000000 : ℝ)+2*(983563502277/629500000000000 : ℝ)*(403/2500 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (6293244584731847909/6295000000000000000 : ℝ)+2*(983563502277/629500000000000 : ℝ)*(403/2500 : ℝ)=(5001124379240023/5000000000000000 : ℝ) by norm_num, show 1+2*(47192672960106519/100000000000000000000 : ℝ)=(50047192672960106519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6293244584731847909/6295000000000000000 : ℝ)*(X 1 0+X 2 0)+(983563502277/629500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (393/4000 : ℝ)) (hi := (403/2500 : ℝ)) (c := (6293244584731847909/6295000000000000000 : ℝ)) (alpha := (983563502277/629500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6293244584731847909/6295000000000000000 : ℝ)*(X 0 1+X 2 1)+(983563502277/629500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (393/4000 : ℝ)) (hi := (403/2500 : ℝ)) (c := (6293244584731847909/6295000000000000000 : ℝ)) (alpha := (983563502277/629500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6293244584731847909/6295000000000000000 : ℝ)*(X 0 2+X 1 2)+(983563502277/629500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (393/4000 : ℝ)) (hi := (403/2500 : ℝ)) (c := (6293244584731847909/6295000000000000000 : ℝ)) (alpha := (983563502277/629500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2045631147/10000000000 : ℝ)*X 0 0+(5427687029/10000000000 : ℝ)*X 0 1+(209235733/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((33455197/62500000 : ℝ)*X 1 0+(-2146217563/10000000000 : ℝ)*X 1 1+(2615446699/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53528313/100000000 : ℝ)*X 2 0+(1046178733/2000000000 : ℝ)*X 2 1+(-1073108751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081644167/2500000000 : ℝ)*X 0 0+(515670911/1250000000 : ℝ)*X 0 1+(283559089/625000000 : ℝ)*X 0 2+(1081644167/2500000000 : ℝ)*X 1 0+(515670911/1250000000 : ℝ)*X 1 1+(283559089/625000000 : ℝ)*X 1 2+(1081644167/2500000000 : ℝ)*X 2 0+(515670911/1250000000 : ℝ)*X 2 1+(283559089/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-204565059/1000000000 : ℝ)*X 0 0+(5231715539/10000000000 : ℝ)*X 0 1+(339178743/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302163643/10000000000 : ℝ)*X 1 0+(-1950251107/10000000000 : ℝ)*X 1 1+(2713430089/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302164519/10000000000 : ℝ)*X 2 0+(2713429807/5000000000 : ℝ)*X 2 1+(-975125343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163309123/5000000000 : ℝ)*X 0 0+(4535225719/10000000000 : ℝ)*X 0 1+(1031774123/2500000000 : ℝ)*X 0 2+(2163309123/5000000000 : ℝ)*X 1 0+(4535225719/10000000000 : ℝ)*X 1 1+(1031774123/2500000000 : ℝ)*X 1 2+(2163309123/5000000000 : ℝ)*X 2 0+(4535225719/10000000000 : ℝ)*X 2 1+(1031774123/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (602119269810770245734977787/78687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68354341/5000000000000 : ℝ)*(base19) + (1105094579/100000000000000 : ℝ)*(base23) + (179692919/100000000000000 : ℝ)*(upper3) + (14223349/50000000000000 : ℝ)*(upper4) + (16787029/10000000000000 : ℝ)*(upper5) + (938901591188927/25000000000000 : ℝ)*(major0) + (938901591188927/25000000000000 : ℝ)*(major1) + (938901591188927/25000000000000 : ℝ)*(major2) + (2540745149941903/50000000000000 : ℝ)*(sp0) + (5081514926028677/100000000000000 : ℝ)*(sp1) + (2540757594010459/50000000000000 : ℝ)*(sp2) + (1214842179247299/50000000000000 : ℝ)*(sp3) + (25993231691/100000000000000 : ℝ)*(sp4) + (591141679/5000000000000 : ℝ)*(sp7) + (1214848090664089/50000000000000 : ℝ)*(f.failure) + (5081516293115497/100000000000000 : ℝ)*(f.sum) + (20907307274573/3934375000000000000000000000 : ℝ)*base66 + (1884475577502431357/157375000000000000000000000000000 : ℝ)*base68 + (1101042904299556357/157375000000000000000000000000000 : ℝ)*base70 + (1004086167665306357/157375000000000000000000000000000 : ℝ)*base72 + (83620353680059/31475000000000000000000000000 : ℝ)*base74 + (1481680920548556357/157375000000000000000000000000000 : ℝ)*base76 + (1673816625070306357/157375000000000000000000000000000 : ℝ)*base78 + (812497768699056357/157375000000000000000000000000000 : ℝ)*base80 + (10142570474373/3934375000000000000000000000 : ℝ)*base82 + (9853373/1250000000000000000000 : ℝ)*base89 + (9853373/1250000000000000000000 : ℝ)*base91 + (9853373/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88986442340251949978914071/78687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308438609/100000000000000 : ℝ)*(base19) + (1640800983/100000000000000 : ℝ)*(base23) + (8495167/5000000000000 : ℝ)*(upper3) + (2351279/1562500000000 : ℝ)*(lower4) + (56888371/50000000000000 : ℝ)*(upper5) + (1893655239398573/50000000000000 : ℝ)*(major0) + (1893655239398573/50000000000000 : ℝ)*(major1) + (1893655239398573/50000000000000 : ℝ)*(major2) + (3055567551/50000000000000 : ℝ)*(sp1) + (27241478897/100000000000000 : ℝ)*(sp2) + (5124413705906441/100000000000000 : ℝ)*(sp4) + (512440728633273/10000000000000 : ℝ)*(sp5) + (5124384823626561/100000000000000 : ℝ)*(sp6) + (245020721399171/10000000000000 : ℝ)*(sp7) + (245020721399171/10000000000000 : ℝ)*(f.failure) + (5124413705906441/100000000000000 : ℝ)*(f.sum) + (3959725027613/1967187500000000000000000000 : ℝ)*base66 + (595717497912906143/314750000000000000000000000000000 : ℝ)*base68 + (3489259489763156143/314750000000000000000000000000000 : ℝ)*base70 + (3278965938002656143/314750000000000000000000000000000 : ℝ)*base72 + (15457033481427/7868750000000000000000000000 : ℝ)*base74 + (999317541101156143/314750000000000000000000000000000 : ℝ)*base76 + (1396860030430406143/314750000000000000000000000000000 : ℝ)*base78 + (2237911202252093857/314750000000000000000000000000000 : ℝ)*base79 + (23693611094529/15737500000000000000000000000 : ℝ)*base82 + (45553/250000000000000000000 : ℝ)*base90 + (45553/250000000000000000000 : ℝ)*base92 + (45553/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (403/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10849/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15013/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1338_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1338_s4_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1023562303/5000000000 : ℝ)*x 0 + (21154473/39062500 : ℝ)*x 1 + (5242054749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023562303/5000000000 : ℝ)^2149 ≤ (6232506902569/50000000000000 : ℝ)^1637 := by
    have hnat : (1023562303 : ℕ)^2149*50000000000000^1637 ≤ 6232506902569^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023562303 5000000000 6232506902569 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21154473/39062500 : ℝ)^2149 ≤ (223513713601/500000000000 : ℝ)^1637 := by
    have hnat : (21154473 : ℕ)^2149*500000000000^1637 ≤ 223513713601^1637*39062500^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21154473 39062500 223513713601 500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242054749/10000000000 : ℝ)^2149 ≤ (2677015216377/6250000000000 : ℝ)^1637 := by
    have hnat : (5242054749 : ℕ)^2149*6250000000000^1637 ≤ 2677015216377^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242054749 10000000000 2677015216377 6250000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1023562303/5000000000 : ℝ), (21154473/39062500 : ℝ), (5242054749/10000000000 : ℝ)] ![(6232506902569/50000000000000 : ℝ), (223513713601/500000000000 : ℝ), (2677015216377/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1023562303/5000000000 : ℝ)|^2149 ≤ (6232506902569/50000000000000 : ℝ)^1637
        have hw : |(-1023562303/5000000000 : ℝ)|=(1023562303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21154473/39062500 : ℝ)|^2149 ≤ (223513713601/500000000000 : ℝ)^1637
        have hw : |(21154473/39062500 : ℝ)|=(21154473/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242054749/10000000000 : ℝ)|^2149 ≤ (2677015216377/6250000000000 : ℝ)^1637
        have hw : |(5242054749/10000000000 : ℝ)|=(5242054749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s4_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349738953/10000000000 : ℝ)*x 0 + (-2135572279/10000000000 : ℝ)*x 1 + (655256823/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349738953/10000000000 : ℝ)^2149 ≤ (43991008678383/100000000000000 : ℝ)^1637 := by
    have hnat : (5349738953 : ℕ)^2149*100000000000000^1637 ≤ 43991008678383^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349738953 10000000000 43991008678383 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135572279/10000000000 : ℝ)^2149 ≤ (13176749616273/100000000000000 : ℝ)^1637 := by
    have hnat : (2135572279 : ℕ)^2149*100000000000000^1637 ≤ 13176749616273^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135572279 10000000000 13176749616273 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655256823/1250000000 : ℝ)^2149 ≤ (42832241692163/100000000000000 : ℝ)^1637 := by
    have hnat : (655256823 : ℕ)^2149*100000000000000^1637 ≤ 42832241692163^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655256823 1250000000 42832241692163 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349738953/10000000000 : ℝ), (-2135572279/10000000000 : ℝ), (655256823/1250000000 : ℝ)] ![(43991008678383/100000000000000 : ℝ), (13176749616273/100000000000000 : ℝ), (42832241692163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349738953/10000000000 : ℝ)|^2149 ≤ (43991008678383/100000000000000 : ℝ)^1637
        have hw : |(5349738953/10000000000 : ℝ)|=(5349738953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135572279/10000000000 : ℝ)|^2149 ≤ (13176749616273/100000000000000 : ℝ)^1637
        have hw : |(-2135572279/10000000000 : ℝ)|=(2135572279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655256823/1250000000 : ℝ)|^2149 ≤ (42832241692163/100000000000000 : ℝ)^1637
        have hw : |(655256823/1250000000 : ℝ)|=(655256823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s4_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674869629/5000000000 : ℝ)*x 0 + (1048410849/2000000000 : ℝ)*x 1 + (-2135572321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674869629/5000000000 : ℝ)^2149 ≤ (43991011970831/100000000000000 : ℝ)^1637 := by
    have hnat : (2674869629 : ℕ)^2149*100000000000000^1637 ≤ 43991011970831^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674869629 5000000000 43991011970831 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048410849/2000000000 : ℝ)^2149 ≤ (42832238055889/100000000000000 : ℝ)^1637 := by
    have hnat : (1048410849 : ℕ)^2149*100000000000000^1637 ≤ 42832238055889^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048410849 2000000000 42832238055889 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135572321/10000000000 : ℝ)^2149 ≤ (1317674995647/10000000000000 : ℝ)^1637 := by
    have hnat : (2135572321 : ℕ)^2149*10000000000000^1637 ≤ 1317674995647^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135572321 10000000000 1317674995647 10000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674869629/5000000000 : ℝ), (1048410849/2000000000 : ℝ), (-2135572321/10000000000 : ℝ)] ![(43991011970831/100000000000000 : ℝ), (42832238055889/100000000000000 : ℝ), (1317674995647/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674869629/5000000000 : ℝ)|^2149 ≤ (43991011970831/100000000000000 : ℝ)^1637
        have hw : |(2674869629/5000000000 : ℝ)|=(2674869629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048410849/2000000000 : ℝ)|^2149 ≤ (42832238055889/100000000000000 : ℝ)^1637
        have hw : |(1048410849/2000000000 : ℝ)|=(1048410849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135572321/10000000000 : ℝ)|^2149 ≤ (1317674995647/10000000000000 : ℝ)^1637
        have hw : |(-2135572321/10000000000 : ℝ)|=(2135572321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s4_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2163741987/5000000000 : ℝ)*x 0 + (2074811273/5000000000 : ℝ)*x 1 + (2256232361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163741987/5000000000 : ℝ)^2149 ≤ (33301349515419/100000000000000 : ℝ)^1637 := by
    have hnat : (2163741987 : ℕ)^2149*100000000000000^1637 ≤ 33301349515419^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163741987 5000000000 33301349515419 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074811273/5000000000 : ℝ)^2149 ≤ (6303244973599/20000000000000 : ℝ)^1637 := by
    have hnat : (2074811273 : ℕ)^2149*20000000000000^1637 ≤ 6303244973599^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074811273 5000000000 6303244973599 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256232361/5000000000 : ℝ)^2149 ≤ (35182425597613/100000000000000 : ℝ)^1637 := by
    have hnat : (2256232361 : ℕ)^2149*100000000000000^1637 ≤ 35182425597613^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256232361 5000000000 35182425597613 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163741987/5000000000 : ℝ), (2074811273/5000000000 : ℝ), (2256232361/5000000000 : ℝ)] ![(33301349515419/100000000000000 : ℝ), (6303244973599/20000000000000 : ℝ), (35182425597613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163741987/5000000000 : ℝ)|^2149 ≤ (33301349515419/100000000000000 : ℝ)^1637
        have hw : |(2163741987/5000000000 : ℝ)|=(2163741987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2074811273/5000000000 : ℝ)|^2149 ≤ (6303244973599/20000000000000 : ℝ)^1637
        have hw : |(2074811273/5000000000 : ℝ)|=(2074811273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2256232361/5000000000 : ℝ)|^2149 ≤ (35182425597613/100000000000000 : ℝ)^1637
        have hw : |(2256232361/5000000000 : ℝ)|=(2256232361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s4_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047138013/10000000000 : ℝ)*x 0 + (2621347071/5000000000 : ℝ)*x 1 + (270745113/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047138013/10000000000 : ℝ)^2149 ≤ (2493024194783/20000000000000 : ℝ)^1637 := by
    have hnat : (2047138013 : ℕ)^2149*20000000000000^1637 ≤ 2493024194783^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047138013 10000000000 2493024194783 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621347071/5000000000 : ℝ)^2149 ≤ (21419551012791/50000000000000 : ℝ)^1637 := by
    have hnat : (2621347071 : ℕ)^2149*50000000000000^1637 ≤ 21419551012791^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621347071 5000000000 21419551012791 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270745113/500000000 : ℝ)^2149 ≤ (22347888496571/50000000000000 : ℝ)^1637 := by
    have hnat : (270745113 : ℕ)^2149*50000000000000^1637 ≤ 22347888496571^1637*500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270745113 500000000 22347888496571 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047138013/10000000000 : ℝ), (2621347071/5000000000 : ℝ), (270745113/500000000 : ℝ)] ![(2493024194783/20000000000000 : ℝ), (21419551012791/50000000000000 : ℝ), (22347888496571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047138013/10000000000 : ℝ)|^2149 ≤ (2493024194783/20000000000000 : ℝ)^1637
        have hw : |(-2047138013/10000000000 : ℝ)|=(2047138013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621347071/5000000000 : ℝ)|^2149 ≤ (21419551012791/50000000000000 : ℝ)^1637
        have hw : |(2621347071/5000000000 : ℝ)|=(2621347071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270745113/500000000 : ℝ)|^2149 ≤ (22347888496571/50000000000000 : ℝ)^1637
        have hw : |(270745113/500000000 : ℝ)|=(270745113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s4_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061014477/2000000000 : ℝ)*x 0 + (-490681133/2500000000 : ℝ)*x 1 + (676862789/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061014477/2000000000 : ℝ)^2149 ≤ (543868347869/1250000000000 : ℝ)^1637 := by
    have hnat : (1061014477 : ℕ)^2149*1250000000000^1637 ≤ 543868347869^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061014477 2000000000 543868347869 1250000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490681133/2500000000 : ℝ)^2149 ≤ (235895091987/2000000000000 : ℝ)^1637 := by
    have hnat : (490681133 : ℕ)^2149*2000000000000^1637 ≤ 235895091987^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490681133 2500000000 235895091987 2000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676862789/1250000000 : ℝ)^2149 ≤ (44695777556607/100000000000000 : ℝ)^1637 := by
    have hnat : (676862789 : ℕ)^2149*100000000000000^1637 ≤ 44695777556607^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676862789 1250000000 44695777556607 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061014477/2000000000 : ℝ), (-490681133/2500000000 : ℝ), (676862789/1250000000 : ℝ)] ![(543868347869/1250000000000 : ℝ), (235895091987/2000000000000 : ℝ), (44695777556607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061014477/2000000000 : ℝ)|^2149 ≤ (543868347869/1250000000000 : ℝ)^1637
        have hw : |(1061014477/2000000000 : ℝ)|=(1061014477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-490681133/2500000000 : ℝ)|^2149 ≤ (235895091987/2000000000000 : ℝ)^1637
        have hw : |(-490681133/2500000000 : ℝ)|=(490681133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676862789/1250000000 : ℝ)|^2149 ≤ (44695777556607/100000000000000 : ℝ)^1637
        have hw : |(676862789/1250000000 : ℝ)|=(676862789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s4_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530507237/1000000000 : ℝ)*x 0 + (5414902353/10000000000 : ℝ)*x 1 + (-122670281/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530507237/1000000000 : ℝ)^2149 ≤ (2175473383401/5000000000000 : ℝ)^1637 := by
    have hnat : (530507237 : ℕ)^2149*5000000000000^1637 ≤ 2175473383401^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530507237 1000000000 2175473383401 5000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414902353/10000000000 : ℝ)^2149 ≤ (44695778000877/100000000000000 : ℝ)^1637 := by
    have hnat : (5414902353 : ℕ)^2149*100000000000000^1637 ≤ 44695778000877^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414902353 10000000000 44695778000877 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122670281/625000000 : ℝ)^2149 ≤ (11794754315349/100000000000000 : ℝ)^1637 := by
    have hnat : (122670281 : ℕ)^2149*100000000000000^1637 ≤ 11794754315349^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122670281 625000000 11794754315349 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530507237/1000000000 : ℝ), (5414902353/10000000000 : ℝ), (-122670281/625000000 : ℝ)] ![(2175473383401/5000000000000 : ℝ), (44695778000877/100000000000000 : ℝ), (11794754315349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530507237/1000000000 : ℝ)|^2149 ≤ (2175473383401/5000000000000 : ℝ)^1637
        have hw : |(530507237/1000000000 : ℝ)|=(530507237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414902353/10000000000 : ℝ)|^2149 ≤ (44695778000877/100000000000000 : ℝ)^1637
        have hw : |(5414902353/10000000000 : ℝ)|=(5414902353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122670281/625000000 : ℝ)|^2149 ≤ (11794754315349/100000000000000 : ℝ)^1637
        have hw : |(-122670281/625000000 : ℝ)|=(122670281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s4_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081877981/2500000000 : ℝ)*x 0 + (2255563481/5000000000 : ℝ)*x 1 + (129717731/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081877981/2500000000 : ℝ)^2149 ≤ (4162703983873/12500000000000 : ℝ)^1637 := by
    have hnat : (1081877981 : ℕ)^2149*12500000000000^1637 ≤ 4162703983873^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081877981 2500000000 4162703983873 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255563481/5000000000 : ℝ)^2149 ≤ (4396091735667/12500000000000 : ℝ)^1637 := by
    have hnat : (2255563481 : ℕ)^2149*12500000000000^1637 ≤ 4396091735667^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255563481 5000000000 4396091735667 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129717731/312500000 : ℝ)^2149 ≤ (15764817111619/50000000000000 : ℝ)^1637 := by
    have hnat : (129717731 : ℕ)^2149*50000000000000^1637 ≤ 15764817111619^1637*312500000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129717731 312500000 15764817111619 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081877981/2500000000 : ℝ), (2255563481/5000000000 : ℝ), (129717731/312500000 : ℝ)] ![(4162703983873/12500000000000 : ℝ), (4396091735667/12500000000000 : ℝ), (15764817111619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081877981/2500000000 : ℝ)|^2149 ≤ (4162703983873/12500000000000 : ℝ)^1637
        have hw : |(1081877981/2500000000 : ℝ)|=(1081877981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255563481/5000000000 : ℝ)|^2149 ≤ (4396091735667/12500000000000 : ℝ)^1637
        have hw : |(2255563481/5000000000 : ℝ)|=(2255563481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129717731/312500000 : ℝ)|^2149 ≤ (15764817111619/50000000000000 : ℝ)^1637
        have hw : |(129717731/312500000 : ℝ)|=(129717731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11087/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10849/100000 : ℝ) ^ (4297/1024 : ℝ) ≤ (8958109920150731/100000000000000000000 : ℝ) := by
    have hpowers : (10849/100000 : ℝ)^4297 ≤ (8958109920150731/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10849 : ℕ)^4297*100000000000000000000^1024 ≤ 8958109920150731^1024*100000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10849 100000 8958109920150731 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10849/100000 : ℝ)) (X := (8958109920150731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15013/100000 : ℝ) ^ (4297/1024 : ℝ) ≤ (2188263066293543/6250000000000000000 : ℝ) := by
    have hpowers : (15013/100000 : ℝ)^4297 ≤ (2188263066293543/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15013 : ℕ)^4297*6250000000000000000^1024 ≤ 2188263066293543^1024*100000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15013 100000 2188263066293543 6250000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15013/100000 : ℝ)) (X := (2188263066293543/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008958109920150731/50000000000000000000 : ℝ) ≤ (5000213462385663/5000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50008958109920150731/50000000000000000000 : ℝ)^1024 ≤ (5000213462385663/5000000000000000 : ℝ)^4297 := by
      have hnat : (50008958109920150731 : ℕ)^1024*5000000000000000^4297 ≤ 5000213462385663^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008958109920150731 50000000000000000000 5000213462385663 5000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000213462385663/5000000000000000 : ℝ)) (X := (50008958109920150731/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043970318980847419/100000000000000000000 : ℝ) ≤ (5000523831377807/5000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (100043970318980847419/100000000000000000000 : ℝ)^1024 ≤ (5000523831377807/5000000000000000 : ℝ)^4297 := by
      have hnat : (100043970318980847419 : ℕ)^1024*5000000000000000^4297 ≤ 5000523831377807^4297*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043970318980847419 100000000000000000000 5000523831377807 5000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000523831377807/5000000000000000 : ℝ)) (X := (100043970318980847419/100000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127188263066293543/3125000000000000000 : ℝ) ≤ (5000834200369951/5000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (3127188263066293543/3125000000000000000 : ℝ)^1024 ≤ (5000834200369951/5000000000000000 : ℝ)^4297 := by
      have hnat : (3127188263066293543 : ℕ)^1024*5000000000000000^4297 ≤ 5000834200369951^4297*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127188263066293543 3125000000000000000 5000834200369951 5000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000834200369951/5000000000000000 : ℝ)) (X := (3127188263066293543/3125000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8958109920150731/100000000000000000000 : ℝ) ≤ ((1040707723549118011/1041000000000000000 : ℝ)+2*(19398062009/13012500000000 : ℝ)*(10849/100000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (1040707723549118011/1041000000000000000 : ℝ)+2*(19398062009/13012500000000 : ℝ)*(10849/100000 : ℝ)=(5000213462385663/5000000000000000 : ℝ) by norm_num, show 1+2*(8958109920150731/100000000000000000000 : ℝ)=(50008958109920150731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2188263066293543/6250000000000000000 : ℝ)+(8958109920150731/100000000000000000000 : ℝ) ≤ ((1040707723549118011/1041000000000000000 : ℝ)+(19398062009/13012500000000 : ℝ)*((15013/100000 : ℝ)+(10849/100000 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (1040707723549118011/1041000000000000000 : ℝ)+(19398062009/13012500000000 : ℝ)*((15013/100000 : ℝ)+(10849/100000 : ℝ))=(5000523831377807/5000000000000000 : ℝ) by norm_num, show 1+(2188263066293543/6250000000000000000 : ℝ)+(8958109920150731/100000000000000000000 : ℝ)=(100043970318980847419/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2188263066293543/6250000000000000000 : ℝ) ≤ ((1040707723549118011/1041000000000000000 : ℝ)+2*(19398062009/13012500000000 : ℝ)*(15013/100000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (1040707723549118011/1041000000000000000 : ℝ)+2*(19398062009/13012500000000 : ℝ)*(15013/100000 : ℝ)=(5000834200369951/5000000000000000 : ℝ) by norm_num, show 1+2*(2188263066293543/6250000000000000000 : ℝ)=(3127188263066293543/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1040707723549118011/1041000000000000000 : ℝ)*(X 1 0+X 2 0)+(19398062009/13012500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (10849/100000 : ℝ)) (hi := (15013/100000 : ℝ)) (c := (1040707723549118011/1041000000000000000 : ℝ)) (alpha := (19398062009/13012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1040707723549118011/1041000000000000000 : ℝ)*(X 0 1+X 2 1)+(19398062009/13012500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (10849/100000 : ℝ)) (hi := (15013/100000 : ℝ)) (c := (1040707723549118011/1041000000000000000 : ℝ)) (alpha := (19398062009/13012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1040707723549118011/1041000000000000000 : ℝ)*(X 0 2+X 1 2)+(19398062009/13012500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (10849/100000 : ℝ)) (hi := (15013/100000 : ℝ)) (c := (1040707723549118011/1041000000000000000 : ℝ)) (alpha := (19398062009/13012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1023562303/5000000000 : ℝ)*X 0 0+(21154473/39062500 : ℝ)*X 0 1+(5242054749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349738953/10000000000 : ℝ)*X 1 0+(-2135572279/10000000000 : ℝ)*X 1 1+(655256823/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674869629/5000000000 : ℝ)*X 2 0+(1048410849/2000000000 : ℝ)*X 2 1+(-2135572321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163741987/5000000000 : ℝ)*X 0 0+(2074811273/5000000000 : ℝ)*X 0 1+(2256232361/5000000000 : ℝ)*X 0 2+(2163741987/5000000000 : ℝ)*X 1 0+(2074811273/5000000000 : ℝ)*X 1 1+(2256232361/5000000000 : ℝ)*X 1 2+(2163741987/5000000000 : ℝ)*X 2 0+(2074811273/5000000000 : ℝ)*X 2 1+(2256232361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2047138013/10000000000 : ℝ)*X 0 0+(2621347071/5000000000 : ℝ)*X 0 1+(270745113/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061014477/2000000000 : ℝ)*X 1 0+(-490681133/2500000000 : ℝ)*X 1 1+(676862789/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530507237/1000000000 : ℝ)*X 2 0+(5414902353/10000000000 : ℝ)*X 2 1+(-122670281/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081877981/2500000000 : ℝ)*X 0 0+(2255563481/5000000000 : ℝ)*X 0 1+(129717731/312500000 : ℝ)*X 0 2+(1081877981/2500000000 : ℝ)*X 1 0+(2255563481/5000000000 : ℝ)*X 1 1+(129717731/312500000 : ℝ)*X 1 2+(1081877981/2500000000 : ℝ)*X 2 0+(2255563481/5000000000 : ℝ)*X 2 1+(129717731/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3482397680379175038363/347000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137810767/6250000000000 : ℝ)*(base19) + (206926311/10000000000000 : ℝ)*(base23) + (70550141/25000000000000 : ℝ)*(lower2) + (168386589/50000000000000 : ℝ)*(upper3) + (6759033/20000000000000 : ℝ)*(lower4) + (426007403348589/10000000000000 : ℝ)*(major0) + (426007403348589/10000000000000 : ℝ)*(major1) + (426007403348589/10000000000000 : ℝ)*(major2) + (5764049590738807/100000000000000 : ℝ)*(sp0) + (2882041547730597/50000000000000 : ℝ)*(sp1) + (1441020807792589/25000000000000 : ℝ)*(sp2) + (2756036808497233/100000000000000 : ℝ)*(sp3) + (17854847329/50000000000000 : ℝ)*(sp4) + (25623516799/100000000000000 : ℝ)*(sp7) + (172253902000877/6250000000000 : ℝ)*(f.failure) + (2882042650216733/50000000000000 : ℝ)*(f.sum) + (1575522766281/173500000000000000000000000 : ℝ)*base66 + (13741031073045493/3470000000000000000000000000000 : ℝ)*base67 + (19382103721015493/3470000000000000000000000000000 : ℝ)*base69 + (35872237045194507/3470000000000000000000000000000 : ℝ)*base72 + (233252700519/173500000000000000000000000 : ℝ)*base74 + (65406450231294507/3470000000000000000000000000000 : ℝ)*base76 + (13619172452785493/3470000000000000000000000000000 : ℝ)*base77 + (84608615981914507/3470000000000000000000000000000 : ℝ)*base80 + (62078889277/173500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (572889/156250000000000000000 : ℝ)*base89 + (572889/156250000000000000000 : ℝ)*base91 + (572889/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74808844552721224886799093/8675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170751171/12500000000000 : ℝ)*(base19) + (989296803/50000000000000 : ℝ)*(base23) + (17769891/12500000000000 : ℝ)*(upper3) + (141638083/50000000000000 : ℝ)*(lower4) + (171476697/100000000000000 : ℝ)*(upper5) + (2145866890273179/50000000000000 : ℝ)*(major0) + (2145866890273179/50000000000000 : ℝ)*(major1) + (2145866890273179/50000000000000 : ℝ)*(major2) + (14879151573/50000000000000 : ℝ)*(sp1) + (41044881989/100000000000000 : ℝ)*(sp2) + (5806922512262029/100000000000000 : ℝ)*(sp4) + (1161378277589903/20000000000000 : ℝ)*(sp5) + (2903439744393217/50000000000000 : ℝ)*(sp6) + (138827238069037/5000000000000 : ℝ)*(sp7) + (138827238069037/5000000000000 : ℝ)*(f.failure) + (5806922512262029/100000000000000 : ℝ)*(f.sum) + (2342241079087/1735000000000000000000000000 : ℝ)*base65 + (147897330210702323/17350000000000000000000000000000 : ℝ)*base67 + (283817757269002323/17350000000000000000000000000000 : ℝ)*base69 + (323292172724452323/17350000000000000000000000000000 : ℝ)*base71 + (1210934509709/867500000000000000000000000 : ℝ)*base74 + (323385917359602323/17350000000000000000000000000000 : ℝ)*base75 + (267158618966302323/17350000000000000000000000000000 : ℝ)*base77 + (287820944161552323/17350000000000000000000000000000 : ℝ)*base79 + (5775492106547/1735000000000000000000000000 : ℝ)*base81 + (1484991/125000000000000000000 : ℝ)*base90 + (1484991/125000000000000000000 : ℝ)*base92 + (1484991/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1338_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1338_s5_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1023691613/5000000000 : ℝ)*x 0 + (5413317199/10000000000 : ℝ)*x 1 + (5244112441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023691613/5000000000 : ℝ)^2149 ≤ (12467081121341/100000000000000 : ℝ)^1637 := by
    have hnat : (1023691613 : ℕ)^2149*100000000000000^1637 ≤ 12467081121341^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023691613 5000000000 12467081121341 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413317199/10000000000 : ℝ)^2149 ≤ (8935720454327/20000000000000 : ℝ)^1637 := by
    have hnat : (5413317199 : ℕ)^2149*20000000000000^1637 ≤ 8935720454327^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413317199 10000000000 8935720454327 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244112441/10000000000 : ℝ)^2149 ≤ (21427158298823/50000000000000 : ℝ)^1637 := by
    have hnat : (5244112441 : ℕ)^2149*50000000000000^1637 ≤ 21427158298823^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244112441 10000000000 21427158298823 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1023691613/5000000000 : ℝ), (5413317199/10000000000 : ℝ), (5244112441/10000000000 : ℝ)] ![(12467081121341/100000000000000 : ℝ), (8935720454327/20000000000000 : ℝ), (21427158298823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1023691613/5000000000 : ℝ)|^2149 ≤ (12467081121341/100000000000000 : ℝ)^1637
        have hw : |(-1023691613/5000000000 : ℝ)|=(1023691613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413317199/10000000000 : ℝ)|^2149 ≤ (8935720454327/20000000000000 : ℝ)^1637
        have hw : |(5413317199/10000000000 : ℝ)|=(5413317199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244112441/10000000000 : ℝ)|^2149 ≤ (21427158298823/50000000000000 : ℝ)^1637
        have hw : |(5244112441/10000000000 : ℝ)|=(5244112441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s5_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349170221/10000000000 : ℝ)*x 0 + (-266700537/1250000000 : ℝ)*x 1 + (5244112687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349170221/10000000000 : ℝ)^2149 ≤ (21992434684569/50000000000000 : ℝ)^1637 := by
    have hnat : (5349170221 : ℕ)^2149*50000000000000^1637 ≤ 21992434684569^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349170221 10000000000 21992434684569 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266700537/1250000000 : ℝ)^2149 ≤ (13160811371477/100000000000000 : ℝ)^1637 := by
    have hnat : (266700537 : ℕ)^2149*100000000000000^1637 ≤ 13160811371477^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266700537 1250000000 13160811371477 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244112687/10000000000 : ℝ)^2149 ≤ (42854319236683/100000000000000 : ℝ)^1637 := by
    have hnat : (5244112687 : ℕ)^2149*100000000000000^1637 ≤ 42854319236683^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244112687 10000000000 42854319236683 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349170221/10000000000 : ℝ), (-266700537/1250000000 : ℝ), (5244112687/10000000000 : ℝ)] ![(21992434684569/50000000000000 : ℝ), (13160811371477/100000000000000 : ℝ), (42854319236683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349170221/10000000000 : ℝ)|^2149 ≤ (21992434684569/50000000000000 : ℝ)^1637
        have hw : |(5349170221/10000000000 : ℝ)|=(5349170221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266700537/1250000000 : ℝ)|^2149 ≤ (13160811371477/100000000000000 : ℝ)^1637
        have hw : |(-266700537/1250000000 : ℝ)|=(266700537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244112687/10000000000 : ℝ)|^2149 ≤ (42854319236683/100000000000000 : ℝ)^1637
        have hw : |(5244112687/10000000000 : ℝ)|=(5244112687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s5_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674584849/5000000000 : ℝ)*x 0 + (5244112901/10000000000 : ℝ)*x 1 + (-213360471/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674584849/5000000000 : ℝ)^2149 ≤ (10996215930897/25000000000000 : ℝ)^1637 := by
    have hnat : (2674584849 : ℕ)^2149*25000000000000^1637 ≤ 10996215930897^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674584849 5000000000 10996215930897 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244112901/10000000000 : ℝ)^2149 ≤ (4285432153243/10000000000000 : ℝ)^1637 := by
    have hnat : (5244112901 : ℕ)^2149*10000000000000^1637 ≤ 4285432153243^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244112901 10000000000 4285432153243 10000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213360471/1000000000 : ℝ)^2149 ≤ (2632162944777/20000000000000 : ℝ)^1637 := by
    have hnat : (213360471 : ℕ)^2149*20000000000000^1637 ≤ 2632162944777^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213360471 1000000000 2632162944777 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674584849/5000000000 : ℝ), (5244112901/10000000000 : ℝ), (-213360471/1000000000 : ℝ)] ![(10996215930897/25000000000000 : ℝ), (4285432153243/10000000000000 : ℝ), (2632162944777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674584849/5000000000 : ℝ)|^2149 ≤ (10996215930897/25000000000000 : ℝ)^1637
        have hw : |(2674584849/5000000000 : ℝ)|=(2674584849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244112901/10000000000 : ℝ)|^2149 ≤ (4285432153243/10000000000000 : ℝ)^1637
        have hw : |(5244112901/10000000000 : ℝ)|=(5244112901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213360471/1000000000 : ℝ)|^2149 ≤ (2632162944777/20000000000000 : ℝ)^1637
        have hw : |(-213360471/1000000000 : ℝ)|=(213360471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s5_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2163818797/5000000000 : ℝ)*x 0 + (4154085941/10000000000 : ℝ)*x 1 + (4507963773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163818797/5000000000 : ℝ)^2149 ≤ (8325725354337/25000000000000 : ℝ)^1637 := by
    have hnat : (2163818797 : ℕ)^2149*25000000000000^1637 ≤ 8325725354337^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163818797 5000000000 8325725354337 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154085941/10000000000 : ℝ)^2149 ≤ (31560734262107/100000000000000 : ℝ)^1637 := by
    have hnat : (4154085941 : ℕ)^2149*100000000000000^1637 ≤ 31560734262107^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154085941 10000000000 31560734262107 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507963773/10000000000 : ℝ)^2149 ≤ (17568182157751/50000000000000 : ℝ)^1637 := by
    have hnat : (4507963773 : ℕ)^2149*50000000000000^1637 ≤ 17568182157751^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507963773 10000000000 17568182157751 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163818797/5000000000 : ℝ), (4154085941/10000000000 : ℝ), (4507963773/10000000000 : ℝ)] ![(8325725354337/25000000000000 : ℝ), (31560734262107/100000000000000 : ℝ), (17568182157751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163818797/5000000000 : ℝ)|^2149 ≤ (8325725354337/25000000000000 : ℝ)^1637
        have hw : |(2163818797/5000000000 : ℝ)|=(2163818797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154085941/10000000000 : ℝ)|^2149 ≤ (31560734262107/100000000000000 : ℝ)^1637
        have hw : |(4154085941/10000000000 : ℝ)|=(4154085941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507963773/10000000000 : ℝ)|^2149 ≤ (17568182157751/50000000000000 : ℝ)^1637
        have hw : |(4507963773/10000000000 : ℝ)|=(4507963773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s5_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1023697567/5000000000 : ℝ)*x 0 + (1311180259/2500000000 : ℝ)*x 1 + (5412705811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023697567/5000000000 : ℝ)^2149 ≤ (623358815581/5000000000000 : ℝ)^1637 := by
    have hnat : (1023697567 : ℕ)^2149*5000000000000^1637 ≤ 623358815581^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023697567 5000000000 623358815581 5000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311180259/2500000000 : ℝ)^2149 ≤ (21430422798131/50000000000000 : ℝ)^1637 := by
    have hnat : (1311180259 : ℕ)^2149*50000000000000^1637 ≤ 21430422798131^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311180259 2500000000 21430422798131 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412705811/10000000000 : ℝ)^2149 ≤ (44671978077101/100000000000000 : ℝ)^1637 := by
    have hnat : (5412705811 : ℕ)^2149*100000000000000^1637 ≤ 44671978077101^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412705811 10000000000 44671978077101 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1023697567/5000000000 : ℝ), (1311180259/2500000000 : ℝ), (5412705811/10000000000 : ℝ)] ![(623358815581/5000000000000 : ℝ), (21430422798131/50000000000000 : ℝ), (44671978077101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1023697567/5000000000 : ℝ)|^2149 ≤ (623358815581/5000000000000 : ℝ)^1637
        have hw : |(-1023697567/5000000000 : ℝ)|=(1023697567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311180259/2500000000 : ℝ)|^2149 ≤ (21430422798131/50000000000000 : ℝ)^1637
        have hw : |(1311180259/2500000000 : ℝ)|=(1311180259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412705811/10000000000 : ℝ)|^2149 ≤ (44671978077101/100000000000000 : ℝ)^1637
        have hw : |(5412705811/10000000000 : ℝ)|=(5412705811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s5_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607087/10000000000 : ℝ)*x 0 + (-1965011173/10000000000 : ℝ)*x 1 + (1082541163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607087/10000000000 : ℝ)^2149 ≤ (2175761243211/5000000000000 : ℝ)^1637 := by
    have hnat : (5305607087 : ℕ)^2149*5000000000000^1637 ≤ 2175761243211^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607087 10000000000 2175761243211 5000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965011173/10000000000 : ℝ)^2149 ≤ (2362559400459/20000000000000 : ℝ)^1637 := by
    have hnat : (1965011173 : ℕ)^2149*20000000000000^1637 ≤ 2362559400459^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965011173 10000000000 2362559400459 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082541163/2000000000 : ℝ)^2149 ≤ (44671978120439/100000000000000 : ℝ)^1637 := by
    have hnat : (1082541163 : ℕ)^2149*100000000000000^1637 ≤ 44671978120439^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082541163 2000000000 44671978120439 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607087/10000000000 : ℝ), (-1965011173/10000000000 : ℝ), (1082541163/2000000000 : ℝ)] ![(2175761243211/5000000000000 : ℝ), (2362559400459/20000000000000 : ℝ), (44671978120439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607087/10000000000 : ℝ)|^2149 ≤ (2175761243211/5000000000000 : ℝ)^1637
        have hw : |(5305607087/10000000000 : ℝ)|=(5305607087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1965011173/10000000000 : ℝ)|^2149 ≤ (2362559400459/20000000000000 : ℝ)^1637
        have hw : |(-1965011173/10000000000 : ℝ)|=(1965011173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082541163/2000000000 : ℝ)|^2149 ≤ (44671978120439/100000000000000 : ℝ)^1637
        have hw : |(1082541163/2000000000 : ℝ)|=(1082541163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s5_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607063/10000000000 : ℝ)*x 0 + (5412705837/10000000000 : ℝ)*x 1 + (-982505587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607063/10000000000 : ℝ)^2149 ≤ (43515224605813/100000000000000 : ℝ)^1637 := by
    have hnat : (5305607063 : ℕ)^2149*100000000000000^1637 ≤ 43515224605813^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607063 10000000000 43515224605813 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412705837/10000000000 : ℝ)^2149 ≤ (22335989179399/50000000000000 : ℝ)^1637 := by
    have hnat : (5412705837 : ℕ)^2149*50000000000000^1637 ≤ 22335989179399^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412705837 10000000000 22335989179399 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982505587/5000000000 : ℝ)^2149 ≤ (11812797010187/100000000000000 : ℝ)^1637 := by
    have hnat : (982505587 : ℕ)^2149*100000000000000^1637 ≤ 11812797010187^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982505587 5000000000 11812797010187 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607063/10000000000 : ℝ), (5412705837/10000000000 : ℝ), (-982505587/5000000000 : ℝ)] ![(43515224605813/100000000000000 : ℝ), (22335989179399/50000000000000 : ℝ), (11812797010187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607063/10000000000 : ℝ)|^2149 ≤ (43515224605813/100000000000000 : ℝ)^1637
        have hw : |(5305607063/10000000000 : ℝ)|=(5305607063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412705837/10000000000 : ℝ)|^2149 ≤ (22335989179399/50000000000000 : ℝ)^1637
        have hw : |(5412705837/10000000000 : ℝ)|=(5412705837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-982505587/5000000000 : ℝ)|^2149 ≤ (11812797010187/100000000000000 : ℝ)^1637
        have hw : |(-982505587/5000000000 : ℝ)|=(982505587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s5_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4327663959/10000000000 : ℝ)*x 0 + (901338271/2000000000 : ℝ)*x 1 + (4155364489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327663959/10000000000 : ℝ)^2149 ≤ (33303167763921/100000000000000 : ℝ)^1637 := by
    have hnat : (4327663959 : ℕ)^2149*100000000000000^1637 ≤ 33303167763921^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327663959 10000000000 33303167763921 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901338271/2000000000 : ℝ)^2149 ≤ (8780836350267/25000000000000 : ℝ)^1637 := by
    have hnat : (901338271 : ℕ)^2149*25000000000000^1637 ≤ 8780836350267^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901338271 2000000000 8780836350267 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155364489/10000000000 : ℝ)^2149 ≤ (493335731559/1562500000000 : ℝ)^1637 := by
    have hnat : (4155364489 : ℕ)^2149*1562500000000^1637 ≤ 493335731559^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155364489 10000000000 493335731559 1562500000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327663959/10000000000 : ℝ), (901338271/2000000000 : ℝ), (4155364489/10000000000 : ℝ)] ![(33303167763921/100000000000000 : ℝ), (8780836350267/25000000000000 : ℝ), (493335731559/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327663959/10000000000 : ℝ)|^2149 ≤ (33303167763921/100000000000000 : ℝ)^1637
        have hw : |(4327663959/10000000000 : ℝ)|=(4327663959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901338271/2000000000 : ℝ)|^2149 ≤ (8780836350267/25000000000000 : ℝ)^1637
        have hw : |(901338271/2000000000 : ℝ)|=(901338271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155364489/10000000000 : ℝ)|^2149 ≤ (493335731559/1562500000000 : ℝ)^1637
        have hw : |(4155364489/10000000000 : ℝ)|=(4155364489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11131/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14713/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11087/100000 : ℝ) ^ (4297/1024 : ℝ) ≤ (9812137715399839/100000000000000000000 : ℝ) := by
    have hpowers : (11087/100000 : ℝ)^4297 ≤ (9812137715399839/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11087 : ℕ)^4297*100000000000000000000^1024 ≤ 9812137715399839^1024*100000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11087 100000 9812137715399839 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11087/100000 : ℝ)) (X := (9812137715399839/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (4297/1024 : ℝ) ≤ (32602144654810869/100000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^4297 ≤ (32602144654810869/100000000000000000000 : ℝ)^1024 := by
      have hnat : (369 : ℕ)^4297*100000000000000000000^1024 ≤ 32602144654810869^1024*2500^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 32602144654810869 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (32602144654810869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009812137715399839/50000000000000000000 : ℝ) ≤ (10000467622907263/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50009812137715399839/50000000000000000000 : ℝ)^1024 ≤ (10000467622907263/10000000000000000 : ℝ)^4297 := by
      have hnat : (50009812137715399839 : ℕ)^1024*10000000000000000^4297 ≤ 10000467622907263^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009812137715399839 50000000000000000000 10000467622907263 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000467622907263/10000000000000000 : ℝ)) (X := (50009812137715399839/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010603570592552677/25000000000000000000 : ℝ) ≤ (5000505296848171/5000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (25010603570592552677/25000000000000000000 : ℝ)^1024 ≤ (5000505296848171/5000000000000000 : ℝ)^4297 := by
      have hnat : (25010603570592552677 : ℕ)^1024*5000000000000000^4297 ≤ 5000505296848171^4297*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010603570592552677 25000000000000000000 5000505296848171 5000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000505296848171/5000000000000000 : ℝ)) (X := (25010603570592552677/25000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032602144654810869/50000000000000000000 : ℝ) ≤ (10001553564485421/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50032602144654810869/50000000000000000000 : ℝ)^1024 ≤ (10001553564485421/10000000000000000 : ℝ)^4297 := by
      have hnat : (50032602144654810869 : ℕ)^1024*10000000000000000^4297 ≤ 10001553564485421^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032602144654810869 50000000000000000000 10001553564485421 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001553564485421/10000000000000000 : ℝ)) (X := (50032602144654810869/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9812137715399839/100000000000000000000 : ℝ) ≤ ((36719677744661339253/36730000000000000000 : ℝ)+2*(542970789079/367300000000000 : ℝ)*(11087/100000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (36719677744661339253/36730000000000000000 : ℝ)+2*(542970789079/367300000000000 : ℝ)*(11087/100000 : ℝ)=(10000467622907263/10000000000000000 : ℝ) by norm_num, show 1+2*(9812137715399839/100000000000000000000 : ℝ)=(50009812137715399839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32602144654810869/100000000000000000000 : ℝ)+(9812137715399839/100000000000000000000 : ℝ) ≤ ((36719677744661339253/36730000000000000000 : ℝ)+(542970789079/367300000000000 : ℝ)*((369/2500 : ℝ)+(11087/100000 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (36719677744661339253/36730000000000000000 : ℝ)+(542970789079/367300000000000 : ℝ)*((369/2500 : ℝ)+(11087/100000 : ℝ))=(5000505296848171/5000000000000000 : ℝ) by norm_num, show 1+(32602144654810869/100000000000000000000 : ℝ)+(9812137715399839/100000000000000000000 : ℝ)=(25010603570592552677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32602144654810869/100000000000000000000 : ℝ) ≤ ((36719677744661339253/36730000000000000000 : ℝ)+2*(542970789079/367300000000000 : ℝ)*(369/2500 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (36719677744661339253/36730000000000000000 : ℝ)+2*(542970789079/367300000000000 : ℝ)*(369/2500 : ℝ)=(10001553564485421/10000000000000000 : ℝ) by norm_num, show 1+2*(32602144654810869/100000000000000000000 : ℝ)=(50032602144654810869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36719677744661339253/36730000000000000000 : ℝ)*(X 1 0+X 2 0)+(542970789079/367300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (36719677744661339253/36730000000000000000 : ℝ)) (alpha := (542970789079/367300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36719677744661339253/36730000000000000000 : ℝ)*(X 0 1+X 2 1)+(542970789079/367300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (36719677744661339253/36730000000000000000 : ℝ)) (alpha := (542970789079/367300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36719677744661339253/36730000000000000000 : ℝ)*(X 0 2+X 1 2)+(542970789079/367300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (36719677744661339253/36730000000000000000 : ℝ)) (alpha := (542970789079/367300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1023691613/5000000000 : ℝ)*X 0 0+(5413317199/10000000000 : ℝ)*X 0 1+(5244112441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349170221/10000000000 : ℝ)*X 1 0+(-266700537/1250000000 : ℝ)*X 1 1+(5244112687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674584849/5000000000 : ℝ)*X 2 0+(5244112901/10000000000 : ℝ)*X 2 1+(-213360471/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163818797/5000000000 : ℝ)*X 0 0+(4154085941/10000000000 : ℝ)*X 0 1+(4507963773/10000000000 : ℝ)*X 0 2+(2163818797/5000000000 : ℝ)*X 1 0+(4154085941/10000000000 : ℝ)*X 1 1+(4507963773/10000000000 : ℝ)*X 1 2+(2163818797/5000000000 : ℝ)*X 2 0+(4154085941/10000000000 : ℝ)*X 2 1+(4507963773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1023697567/5000000000 : ℝ)*X 0 0+(1311180259/2500000000 : ℝ)*X 0 1+(5412705811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305607087/10000000000 : ℝ)*X 1 0+(-1965011173/10000000000 : ℝ)*X 1 1+(1082541163/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305607063/10000000000 : ℝ)*X 2 0+(5412705837/10000000000 : ℝ)*X 2 1+(-982505587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327663959/10000000000 : ℝ)*X 0 0+(901338271/2000000000 : ℝ)*X 0 1+(4155364489/10000000000 : ℝ)*X 0 2+(4327663959/10000000000 : ℝ)*X 1 0+(901338271/2000000000 : ℝ)*X 1 1+(4155364489/10000000000 : ℝ)*X 1 2+(4327663959/10000000000 : ℝ)*X 2 0+(901338271/2000000000 : ℝ)*X 2 1+(4155364489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47668281239917220495709/4591250000000000000000000000 : ℝ) := by norm_num
    linear_combination (994994001/50000000000000 : ℝ)*(base19) + (356005343/25000000000000 : ℝ)*(base23) + (180871613/100000000000000 : ℝ)*(upper2) + (298604809/50000000000000 : ℝ)*(upper3) + (87259723/50000000000000 : ℝ)*(upper4) + (2183989020602981/50000000000000 : ℝ)*(major0) + (2183989020602981/50000000000000 : ℝ)*(major1) + (2183989020602981/50000000000000 : ℝ)*(major2) + (5910055279117753/100000000000000 : ℝ)*(sp0) + (147752065641327/2500000000000 : ℝ)*(sp1) + (591008319161971/10000000000000 : ℝ)*(sp2) + (706462298262753/25000000000000 : ℝ)*(sp3) + (29336523329/100000000000000 : ℝ)*(sp4) + (21927639187/100000000000000 : ℝ)*(sp7) + (2825871120690199/100000000000000 : ℝ)*(f.failure) + (2955042307820541/50000000000000 : ℝ)*(f.sum) + (153869151561093/18365000000000000000000000000 : ℝ)*base65 + (17124781124817986807/1836500000000000000000000000000000 : ℝ)*base68 + (153528968587486807/1836500000000000000000000000000000 : ℝ)*base70 + (31053034696067513193/1836500000000000000000000000000000 : ℝ)*base71 + (55119127090907/18365000000000000000000000000 : ℝ)*base74 + (8915115252530513193/1836500000000000000000000000000000 : ℝ)*base75 + (23599384759217513193/1836500000000000000000000000000000 : ℝ)*base77 + (1927185363711486807/1836500000000000000000000000000000 : ℝ)*base80 + (77967149761063/18365000000000000000000000000 : ℝ)*base81 + (17761357/2500000000000000000000 : ℝ)*base90 + (17761357/2500000000000000000000 : ℝ)*base92 + (17761357/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (531665712471956960048172081/114781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (853635921/100000000000000 : ℝ)*(base19) + (868260977/100000000000000 : ℝ)*(base23) + (847669/800000000000 : ℝ)*(upper3) + (3584671/20000000000000 : ℝ)*(lower4) + (46043389/50000000000000 : ℝ)*(upper5) + (274977242084497/6250000000000 : ℝ)*(major0) + (274977242084497/6250000000000 : ℝ)*(major1) + (274977242084497/6250000000000 : ℝ)*(major2) + (8541583361/50000000000000 : ℝ)*(sp1) + (18029845737/100000000000000 : ℝ)*(sp2) + (2976459690552297/50000000000000 : ℝ)*(sp4) + (5952901444301951/100000000000000 : ℝ)*(sp5) + (148822512074947/2500000000000 : ℝ)*(sp6) + (2846352211199599/100000000000000 : ℝ)*(sp7) + (2846352211199599/100000000000000 : ℝ)*(f.failure) + (2976459690552297/50000000000000 : ℝ)*(f.sum) + (19166319276217/18365000000000000000000000000 : ℝ)*base66 + (5176942676202848241/229562500000000000000000000000000 : ℝ)*base67 + (3083807958729848241/229562500000000000000000000000000 : ℝ)*base69 + (3826918048358910741/229562500000000000000000000000000 : ℝ)*base71 + (33558763726279/9182500000000000000000000000 : ℝ)*base73 + (735991615593285741/229562500000000000000000000000000 : ℝ)*base75 + (883285959259473241/229562500000000000000000000000000 : ℝ)*base77 + (4784817968118535741/229562500000000000000000000000000 : ℝ)*base79 + (57251668690957/18365000000000000000000000000 : ℝ)*base82 + (17345557/2500000000000000000000 : ℝ)*base90 + (17345557/2500000000000000000000 : ℝ)*base92 + (17345557/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1338_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1338_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (403/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1338_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1338_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1338_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (403/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (393/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1338_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
