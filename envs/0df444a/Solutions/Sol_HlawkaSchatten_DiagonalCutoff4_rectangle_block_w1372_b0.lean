-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1372_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:42.260396+00:00
-- url     : https://prove2.me/submissions/960d800b-987a-4a79-8202-f632728c1311

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
theorem support_rectangle_w1372_s0_0 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-223942899/1250000000 : ℝ)*x 0 + (1196812061/2000000000 : ℝ)*x 1 + (2409008063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223942899/1250000000 : ℝ)^1083 ≤ (657569807613/6250000000000 : ℝ)^827 := by
    have hnat : (223942899 : ℕ)^1083*6250000000000^827 ≤ 657569807613^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223942899 1250000000 657569807613 6250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1196812061/2000000000 : ℝ)^1083 ≤ (12761581263573/25000000000000 : ℝ)^827 := by
    have hnat : (1196812061 : ℕ)^1083*25000000000000^827 ≤ 12761581263573^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196812061 2000000000 12761581263573 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2409008063/5000000000 : ℝ)^1083 ≤ (9608139501883/25000000000000 : ℝ)^827 := by
    have hnat : (2409008063 : ℕ)^1083*25000000000000^827 ≤ 9608139501883^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409008063 5000000000 9608139501883 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223942899/1250000000 : ℝ), (1196812061/2000000000 : ℝ), (2409008063/5000000000 : ℝ)] ![(657569807613/6250000000000 : ℝ), (12761581263573/25000000000000 : ℝ), (9608139501883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223942899/1250000000 : ℝ)|^1083 ≤ (657569807613/6250000000000 : ℝ)^827
        have hw : |(-223942899/1250000000 : ℝ)|=(223942899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1196812061/2000000000 : ℝ)|^1083 ≤ (12761581263573/25000000000000 : ℝ)^827
        have hw : |(1196812061/2000000000 : ℝ)|=(1196812061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2409008063/5000000000 : ℝ)|^1083 ≤ (9608139501883/25000000000000 : ℝ)^827
        have hw : |(2409008063/5000000000 : ℝ)|=(2409008063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s0_1 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (109969123/200000000 : ℝ)*x 0 + (-1226442683/5000000000 : ℝ)*x 1 + (4818016717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109969123/200000000 : ℝ)^1083 ≤ (1427846894741/3125000000000 : ℝ)^827 := by
    have hnat : (109969123 : ℕ)^1083*3125000000000^827 ≤ 1427846894741^827*200000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109969123 200000000 1427846894741 3125000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226442683/5000000000 : ℝ)^1083 ≤ (158763351733/1000000000000 : ℝ)^827 := by
    have hnat : (1226442683 : ℕ)^1083*1000000000000^827 ≤ 158763351733^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226442683 5000000000 158763351733 1000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4818016717/10000000000 : ℝ)^1083 ≤ (19216282090587/50000000000000 : ℝ)^827 := by
    have hnat : (4818016717 : ℕ)^1083*50000000000000^827 ≤ 19216282090587^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818016717 10000000000 19216282090587 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109969123/200000000 : ℝ), (-1226442683/5000000000 : ℝ), (4818016717/10000000000 : ℝ)] ![(1427846894741/3125000000000 : ℝ), (158763351733/1000000000000 : ℝ), (19216282090587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109969123/200000000 : ℝ)|^1083 ≤ (1427846894741/3125000000000 : ℝ)^827
        have hw : |(109969123/200000000 : ℝ)|=(109969123/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1226442683/5000000000 : ℝ)|^1083 ≤ (158763351733/1000000000000 : ℝ)^827
        have hw : |(-1226442683/5000000000 : ℝ)|=(1226442683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4818016717/10000000000 : ℝ)|^1083 ≤ (19216282090587/50000000000000 : ℝ)^827
        have hw : |(4818016717/10000000000 : ℝ)|=(4818016717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s0_2 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5498456039/10000000000 : ℝ)*x 0 + (4818016049/10000000000 : ℝ)*x 1 + (-613221583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5498456039/10000000000 : ℝ)^1083 ≤ (11422774855949/25000000000000 : ℝ)^827 := by
    have hnat : (5498456039 : ℕ)^1083*25000000000000^827 ≤ 11422774855949^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498456039 10000000000 11422774855949 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4818016049/10000000000 : ℝ)^1083 ≤ (38432557203183/100000000000000 : ℝ)^827 := by
    have hnat : (4818016049 : ℕ)^1083*100000000000000^827 ≤ 38432557203183^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818016049 10000000000 38432557203183 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (613221583/2500000000 : ℝ)^1083 ≤ (15876343361211/100000000000000 : ℝ)^827 := by
    have hnat : (613221583 : ℕ)^1083*100000000000000^827 ≤ 15876343361211^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613221583 2500000000 15876343361211 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5498456039/10000000000 : ℝ), (4818016049/10000000000 : ℝ), (-613221583/2500000000 : ℝ)] ![(11422774855949/25000000000000 : ℝ), (38432557203183/100000000000000 : ℝ), (15876343361211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5498456039/10000000000 : ℝ)|^1083 ≤ (11422774855949/25000000000000 : ℝ)^827
        have hw : |(5498456039/10000000000 : ℝ)|=(5498456039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4818016049/10000000000 : ℝ)|^1083 ≤ (38432557203183/100000000000000 : ℝ)^827
        have hw : |(4818016049/10000000000 : ℝ)|=(4818016049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-613221583/2500000000 : ℝ)|^1083 ≤ (15876343361211/100000000000000 : ℝ)^827
        have hw : |(-613221583/2500000000 : ℝ)|=(613221583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s0_3 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1043572571/2500000000 : ℝ)*x 0 + (776302973/2500000000 : ℝ)*x 1 + (5575171071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043572571/2500000000 : ℝ)^1083 ≤ (15925864756419/50000000000000 : ℝ)^827 := by
    have hnat : (1043572571 : ℕ)^1083*50000000000000^827 ≤ 15925864756419^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043572571 2500000000 15925864756419 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776302973/2500000000 : ℝ)^1083 ≤ (21620551302223/100000000000000 : ℝ)^827 := by
    have hnat : (776302973 : ℕ)^1083*100000000000000^827 ≤ 21620551302223^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776302973 2500000000 21620551302223 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5575171071/10000000000 : ℝ)^1083 ≤ (46527719167687/100000000000000 : ℝ)^827 := by
    have hnat : (5575171071 : ℕ)^1083*100000000000000^827 ≤ 46527719167687^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5575171071 10000000000 46527719167687 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043572571/2500000000 : ℝ), (776302973/2500000000 : ℝ), (5575171071/10000000000 : ℝ)] ![(15925864756419/50000000000000 : ℝ), (21620551302223/100000000000000 : ℝ), (46527719167687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043572571/2500000000 : ℝ)|^1083 ≤ (15925864756419/50000000000000 : ℝ)^827
        have hw : |(1043572571/2500000000 : ℝ)|=(1043572571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776302973/2500000000 : ℝ)|^1083 ≤ (21620551302223/100000000000000 : ℝ)^827
        have hw : |(776302973/2500000000 : ℝ)|=(776302973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5575171071/10000000000 : ℝ)|^1083 ≤ (46527719167687/100000000000000 : ℝ)^827
        have hw : |(5575171071/10000000000 : ℝ)|=(5575171071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s0_4 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-448961217/2500000000 : ℝ)*x 0 + (4847971109/10000000000 : ℝ)*x 1 + (1488258681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448961217/2500000000 : ℝ)^1083 ≤ (10554211472317/100000000000000 : ℝ)^827 := by
    have hnat : (448961217 : ℕ)^1083*100000000000000^827 ≤ 10554211472317^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448961217 2500000000 10554211472317 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4847971109/10000000000 : ℝ)^1083 ≤ (19372885650569/50000000000000 : ℝ)^827 := by
    have hnat : (4847971109 : ℕ)^1083*50000000000000^827 ≤ 19372885650569^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4847971109 10000000000 19372885650569 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1488258681/2500000000 : ℝ)^1083 ≤ (50700017212947/100000000000000 : ℝ)^827 := by
    have hnat : (1488258681 : ℕ)^1083*100000000000000^827 ≤ 50700017212947^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488258681 2500000000 50700017212947 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448961217/2500000000 : ℝ), (4847971109/10000000000 : ℝ), (1488258681/2500000000 : ℝ)] ![(10554211472317/100000000000000 : ℝ), (19372885650569/50000000000000 : ℝ), (50700017212947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448961217/2500000000 : ℝ)|^1083 ≤ (10554211472317/100000000000000 : ℝ)^827
        have hw : |(-448961217/2500000000 : ℝ)|=(448961217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4847971109/10000000000 : ℝ)|^1083 ≤ (19372885650569/50000000000000 : ℝ)^827
        have hw : |(4847971109/10000000000 : ℝ)|=(4847971109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1488258681/2500000000 : ℝ)|^1083 ≤ (50700017212947/100000000000000 : ℝ)^827
        have hw : |(1488258681/2500000000 : ℝ)|=(1488258681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s0_5 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (647561429/1250000000 : ℝ)*x 0 + (-65893499/500000000 : ℝ)*x 1 + (5953033473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647561429/1250000000 : ℝ)^1083 ≤ (42262360260217/100000000000000 : ℝ)^827 := by
    have hnat : (647561429 : ℕ)^1083*100000000000000^827 ≤ 42262360260217^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647561429 1250000000 42262360260217 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65893499/500000000 : ℝ)^1083 ≤ (3518818236047/50000000000000 : ℝ)^827 := by
    have hnat : (65893499 : ℕ)^1083*50000000000000^827 ≤ 3518818236047^827*500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65893499 500000000 3518818236047 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5953033473/10000000000 : ℝ)^1083 ≤ (25350001630257/50000000000000 : ℝ)^827 := by
    have hnat : (5953033473 : ℕ)^1083*50000000000000^827 ≤ 25350001630257^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5953033473 10000000000 25350001630257 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647561429/1250000000 : ℝ), (-65893499/500000000 : ℝ), (5953033473/10000000000 : ℝ)] ![(42262360260217/100000000000000 : ℝ), (3518818236047/50000000000000 : ℝ), (25350001630257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647561429/1250000000 : ℝ)|^1083 ≤ (42262360260217/100000000000000 : ℝ)^827
        have hw : |(647561429/1250000000 : ℝ)|=(647561429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65893499/500000000 : ℝ)|^1083 ≤ (3518818236047/50000000000000 : ℝ)^827
        have hw : |(-65893499/500000000 : ℝ)|=(65893499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5953033473/10000000000 : ℝ)|^1083 ≤ (25350001630257/50000000000000 : ℝ)^827
        have hw : |(5953033473/10000000000 : ℝ)|=(5953033473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s0_6 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2590245217/5000000000 : ℝ)*x 0 + (5953035797/10000000000 : ℝ)*x 1 + (-658933899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590245217/5000000000 : ℝ)^1083 ≤ (10565587399569/25000000000000 : ℝ)^827 := by
    have hnat : (2590245217 : ℕ)^1083*25000000000000^827 ≤ 10565587399569^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590245217 5000000000 10565587399569 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5953035797/10000000000 : ℝ)^1083 ≤ (25350014590071/50000000000000 : ℝ)^827 := by
    have hnat : (5953035797 : ℕ)^1083*50000000000000^827 ≤ 25350014590071^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5953035797 10000000000 25350014590071 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658933899/5000000000 : ℝ)^1083 ≤ (7037621212891/100000000000000 : ℝ)^827 := by
    have hnat : (658933899 : ℕ)^1083*100000000000000^827 ≤ 7037621212891^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658933899 5000000000 7037621212891 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590245217/5000000000 : ℝ), (5953035797/10000000000 : ℝ), (-658933899/5000000000 : ℝ)] ![(10565587399569/25000000000000 : ℝ), (25350014590071/50000000000000 : ℝ), (7037621212891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590245217/5000000000 : ℝ)|^1083 ≤ (10565587399569/25000000000000 : ℝ)^827
        have hw : |(2590245217/5000000000 : ℝ)|=(2590245217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5953035797/10000000000 : ℝ)|^1083 ≤ (25350014590071/50000000000000 : ℝ)^827
        have hw : |(5953035797/10000000000 : ℝ)|=(5953035797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658933899/5000000000 : ℝ)|^1083 ≤ (7037621212891/100000000000000 : ℝ)^827
        have hw : |(-658933899/5000000000 : ℝ)|=(658933899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s0_7 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4183394679/10000000000 : ℝ)*x 0 + (2755861067/5000000000 : ℝ)*x 1 + (3170932923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183394679/10000000000 : ℝ)^1083 ≤ (6388547140039/20000000000000 : ℝ)^827 := by
    have hnat : (4183394679 : ℕ)^1083*20000000000000^827 ≤ 6388547140039^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183394679 10000000000 6388547140039 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755861067/5000000000 : ℝ)^1083 ≤ (4583551663647/10000000000000 : ℝ)^827 := by
    have hnat : (2755861067 : ℕ)^1083*10000000000000^827 ≤ 4583551663647^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755861067 5000000000 4583551663647 10000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3170932923/10000000000 : ℝ)^1083 ≤ (22221747643967/100000000000000 : ℝ)^827 := by
    have hnat : (3170932923 : ℕ)^1083*100000000000000^827 ≤ 22221747643967^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170932923 10000000000 22221747643967 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183394679/10000000000 : ℝ), (2755861067/5000000000 : ℝ), (3170932923/10000000000 : ℝ)] ![(6388547140039/20000000000000 : ℝ), (4583551663647/10000000000000 : ℝ), (22221747643967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183394679/10000000000 : ℝ)|^1083 ≤ (6388547140039/20000000000000 : ℝ)^827
        have hw : |(4183394679/10000000000 : ℝ)|=(4183394679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755861067/5000000000 : ℝ)|^1083 ≤ (4583551663647/10000000000000 : ℝ)^827
        have hw : |(2755861067/5000000000 : ℝ)|=(2755861067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3170932923/10000000000 : ℝ)|^1083 ≤ (22221747643967/100000000000000 : ℝ)^827
        have hw : |(3170932923/10000000000 : ℝ)|=(3170932923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1372_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1637/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26657/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4331/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4331 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4331*1^1024 ≤ 0^1024*1^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4331/1024 : ℝ) ≤ (1037255739386608371/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4331 ≤ (1037255739386608371/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4331*50000000000000000000^1024 ≤ 1037255739386608371^1024*5^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1037255739386608371 50000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1037255739386608371/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4331 := by
      have hnat : (1 : ℕ)^1024*1^4331 ≤ 1^4331*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51037255739386608371/50000000000000000000 : ℝ) ≤ (10048664911691871/10000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (51037255739386608371/50000000000000000000 : ℝ)^1024 ≤ (10048664911691871/10000000000000000 : ℝ)^4331 := by
      have hnat : (51037255739386608371 : ℕ)^1024*10000000000000000^4331 ≤ 10048664911691871^4331*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51037255739386608371 50000000000000000000 10048664911691871 10000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048664911691871/10000000000000000 : ℝ)) (X := (51037255739386608371/50000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26037255739386608371/25000000000000000000 : ℝ) ≤ (5048664911691871/5000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (26037255739386608371/25000000000000000000 : ℝ)^1024 ≤ (5048664911691871/5000000000000000 : ℝ)^4331 := by
      have hnat : (26037255739386608371 : ℕ)^1024*5000000000000000^4331 ≤ 5048664911691871^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26037255739386608371 25000000000000000000 5048664911691871 5000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048664911691871/5000000000000000 : ℝ)) (X := (26037255739386608371/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(48664911691871/4000000000000000 : ℝ)*(0 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48664911691871/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1037255739386608371/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(48664911691871/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4331/1024 : ℝ) := by
    rw [show (1 : ℝ)+(48664911691871/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10048664911691871/10000000000000000 : ℝ) by norm_num, show 1+(1037255739386608371/50000000000000000000 : ℝ)+(0 : ℝ)=(51037255739386608371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1037255739386608371/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(48664911691871/4000000000000000 : ℝ)*(2/5 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48664911691871/4000000000000000 : ℝ)*(2/5 : ℝ)=(5048664911691871/5000000000000000 : ℝ) by norm_num, show 1+2*(1037255739386608371/50000000000000000000 : ℝ)=(26037255739386608371/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(48664911691871/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48664911691871/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(48664911691871/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48664911691871/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(48664911691871/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48664911691871/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-223942899/1250000000 : ℝ)*X 0 0+(1196812061/2000000000 : ℝ)*X 0 1+(2409008063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((109969123/200000000 : ℝ)*X 1 0+(-1226442683/5000000000 : ℝ)*X 1 1+(4818016717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5498456039/10000000000 : ℝ)*X 2 0+(4818016049/10000000000 : ℝ)*X 2 1+(-613221583/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1043572571/2500000000 : ℝ)*X 0 0+(776302973/2500000000 : ℝ)*X 0 1+(5575171071/10000000000 : ℝ)*X 0 2+(1043572571/2500000000 : ℝ)*X 1 0+(776302973/2500000000 : ℝ)*X 1 1+(5575171071/10000000000 : ℝ)*X 1 2+(1043572571/2500000000 : ℝ)*X 2 0+(776302973/2500000000 : ℝ)*X 2 1+(5575171071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-448961217/2500000000 : ℝ)*X 0 0+(4847971109/10000000000 : ℝ)*X 0 1+(1488258681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((647561429/1250000000 : ℝ)*X 1 0+(-65893499/500000000 : ℝ)*X 1 1+(5953033473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2590245217/5000000000 : ℝ)*X 2 0+(5953035797/10000000000 : ℝ)*X 2 1+(-658933899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4183394679/10000000000 : ℝ)*X 0 0+(2755861067/5000000000 : ℝ)*X 0 1+(3170932923/10000000000 : ℝ)*X 0 2+(4183394679/10000000000 : ℝ)*X 1 0+(2755861067/5000000000 : ℝ)*X 1 1+(3170932923/10000000000 : ℝ)*X 1 2+(4183394679/10000000000 : ℝ)*X 2 0+(2755861067/5000000000 : ℝ)*X 2 1+(3170932923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4091549079897339126279/800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40392539/20000000000000 : ℝ)*(base1) + (11033433/100000000000000 : ℝ)*(base16) + (587215533/50000000000000 : ℝ)*(base19) + (584075793/50000000000000 : ℝ)*(base23) + (218806967/100000000000000 : ℝ)*(upper3) + (631237935755187/100000000000000 : ℝ)*(major0) + (631237935755187/100000000000000 : ℝ)*(major1) + (157809483938797/25000000000000 : ℝ)*(major2) + (8576046629233/1000000000000 : ℝ)*(sp0) + (107200781505773/12500000000000 : ℝ)*(sp1) + (857606269359097/100000000000000 : ℝ)*(sp2) + (80973237632929/20000000000000 : ℝ)*(sp3) + (2976550077/100000000000000 : ℝ)*(sp4) + (374678227/20000000000000 : ℝ)*(sp7) + (16194730540739/4000000000000 : ℝ)*(f.failure) + (857607437510683/100000000000000 : ℝ)*(f.sum) + (1617049471507/3200000000000000000000000000 : ℝ)*base66 + (139502945880813/100000000000000000000000000000 : ℝ)*base68 + (1585459454784877/400000000000000000000000000000 : ℝ)*base69 + (685026858080813/100000000000000000000000000000 : ℝ)*base72 + (5569515637907/3200000000000000000000000000 : ℝ)*base74 + (1521040102784877/400000000000000000000000000000 : ℝ)*base75 + (1612934417215123/400000000000000000000000000000 : ℝ)*base78 + (2091803039215123/400000000000000000000000000000 : ℝ)*base80 + (802139805215123/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4738487/400000000000000000000 : ℝ)*base89 + (4738487/400000000000000000000 : ℝ)*base91 + (738487/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (857029894547650258908837/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (818087591/100000000000000 : ℝ)*(base19) + (1354774731/100000000000000 : ℝ)*(base23) + (258149321/50000000000000 : ℝ)*(base39) + (39559593/50000000000000 : ℝ)*(upper2) + (301021837/100000000000000 : ℝ)*(upper5) + (10407254498073/1562500000000 : ℝ)*(major0) + (10407254498073/1562500000000 : ℝ)*(major1) + (66606377157803/10000000000000 : ℝ)*(major2) + (383908919/20000000000000 : ℝ)*(sp1) + (2801258147/100000000000000 : ℝ)*(sp2) + (452461157751979/50000000000000 : ℝ)*(sp4) + (226229894467943/25000000000000 : ℝ)*(sp5) + (452459337884861/50000000000000 : ℝ)*(sp6) + (427205458274109/100000000000000 : ℝ)*(sp7) + (427205458274109/100000000000000 : ℝ)*(f.failure) + (4524614159013/500000000000 : ℝ)*(f.sum) + (415776559663721/200000000000000000000000000000 : ℝ)*base65 + (49777958199413/40000000000000000000000000000 : ℝ)*base67 + (28456836979167/6250000000000000000000000000 : ℝ)*base70 + (36548231280587/40000000000000000000000000000 : ℝ)*base72 + (687726797863721/200000000000000000000000000000 : ℝ)*base73 + (34840469347917/6250000000000000000000000000 : ℝ)*base76 + (23281692560417/6250000000000000000000000000 : ℝ)*base78 + (4498537745833/6250000000000000000000000000 : ℝ)*base79 + (1261278841927/781250000000000000000000000 : ℝ)*base81 + (21957303/10000000000000000000000 : ℝ)*base90 + (21957303/10000000000000000000000 : ℝ)*base92 + (21957303/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1372_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1637/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26657/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1372_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1372_s1_0 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-986018633/5000000000 : ℝ)*x 0 + (2814468501/5000000000 : ℝ)*x 1 + (2528757721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986018633/5000000000 : ℝ)^1083 ≤ (2982594879453/25000000000000 : ℝ)^827 := by
    have hnat : (986018633 : ℕ)^1083*25000000000000^827 ≤ 2982594879453^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986018633 5000000000 2982594879453 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2814468501/5000000000 : ℝ)^1083 ≤ (23558098434873/50000000000000 : ℝ)^827 := by
    have hnat : (2814468501 : ℕ)^1083*50000000000000^827 ≤ 23558098434873^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814468501 5000000000 23558098434873 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2528757721/5000000000 : ℝ)^1083 ≤ (2559588974619/6250000000000 : ℝ)^827 := by
    have hnat : (2528757721 : ℕ)^1083*6250000000000^827 ≤ 2559588974619^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528757721 5000000000 2559588974619 6250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986018633/5000000000 : ℝ), (2814468501/5000000000 : ℝ), (2528757721/5000000000 : ℝ)] ![(2982594879453/25000000000000 : ℝ), (23558098434873/50000000000000 : ℝ), (2559588974619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986018633/5000000000 : ℝ)|^1083 ≤ (2982594879453/25000000000000 : ℝ)^827
        have hw : |(-986018633/5000000000 : ℝ)|=(986018633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2814468501/5000000000 : ℝ)|^1083 ≤ (23558098434873/50000000000000 : ℝ)^827
        have hw : |(2814468501/5000000000 : ℝ)|=(2814468501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2528757721/5000000000 : ℝ)|^1083 ≤ (2559588974619/6250000000000 : ℝ)^827
        have hw : |(2528757721/5000000000 : ℝ)|=(2528757721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s1_1 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5402607969/10000000000 : ℝ)*x 0 + (-2276194419/10000000000 : ℝ)*x 1 + (5057516743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402607969/10000000000 : ℝ)^1083 ≤ (89301788077/200000000000 : ℝ)^827 := by
    have hnat : (5402607969 : ℕ)^1083*200000000000^827 ≤ 89301788077^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402607969 10000000000 89301788077 200000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276194419/10000000000 : ℝ)^1083 ≤ (7197834272779/50000000000000 : ℝ)^827 := by
    have hnat : (2276194419 : ℕ)^1083*50000000000000^827 ≤ 7197834272779^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276194419 10000000000 7197834272779 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057516743/10000000000 : ℝ)^1083 ≤ (20476718694953/50000000000000 : ℝ)^827 := by
    have hnat : (5057516743 : ℕ)^1083*50000000000000^827 ≤ 20476718694953^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057516743 10000000000 20476718694953 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402607969/10000000000 : ℝ), (-2276194419/10000000000 : ℝ), (5057516743/10000000000 : ℝ)] ![(89301788077/200000000000 : ℝ), (7197834272779/50000000000000 : ℝ), (20476718694953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402607969/10000000000 : ℝ)|^1083 ≤ (89301788077/200000000000 : ℝ)^827
        have hw : |(5402607969/10000000000 : ℝ)|=(5402607969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276194419/10000000000 : ℝ)|^1083 ≤ (7197834272779/50000000000000 : ℝ)^827
        have hw : |(-2276194419/10000000000 : ℝ)|=(2276194419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5057516743/10000000000 : ℝ)|^1083 ≤ (20476718694953/50000000000000 : ℝ)^827
        have hw : |(5057516743/10000000000 : ℝ)|=(5057516743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s1_2 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2701304223/5000000000 : ℝ)*x 0 + (2528757819/5000000000 : ℝ)*x 1 + (-569048803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701304223/5000000000 : ℝ)^1083 ≤ (8930179840219/20000000000000 : ℝ)^827 := by
    have hnat : (2701304223 : ℕ)^1083*20000000000000^827 ≤ 8930179840219^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701304223 5000000000 8930179840219 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2528757819/5000000000 : ℝ)^1083 ≤ (20476712836159/50000000000000 : ℝ)^827 := by
    have hnat : (2528757819 : ℕ)^1083*50000000000000^827 ≤ 20476712836159^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528757819 5000000000 20476712836159 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569048803/2500000000 : ℝ)^1083 ≤ (14395675113339/100000000000000 : ℝ)^827 := by
    have hnat : (569048803 : ℕ)^1083*100000000000000^827 ≤ 14395675113339^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569048803 2500000000 14395675113339 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701304223/5000000000 : ℝ), (2528757819/5000000000 : ℝ), (-569048803/2500000000 : ℝ)] ![(8930179840219/20000000000000 : ℝ), (20476712836159/50000000000000 : ℝ), (14395675113339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701304223/5000000000 : ℝ)|^1083 ≤ (8930179840219/20000000000000 : ℝ)^827
        have hw : |(2701304223/5000000000 : ℝ)|=(2701304223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2528757819/5000000000 : ℝ)|^1083 ≤ (20476712836159/50000000000000 : ℝ)^827
        have hw : |(2528757819/5000000000 : ℝ)|=(2528757819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-569048803/2500000000 : ℝ)|^1083 ≤ (14395675113339/100000000000000 : ℝ)^827
        have hw : |(-569048803/2500000000 : ℝ)|=(569048803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s1_3 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2143469879/5000000000 : ℝ)*x 0 + (3720816487/10000000000 : ℝ)*x 1 + (2465609363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143469879/5000000000 : ℝ)^1083 ≤ (32982050020957/100000000000000 : ℝ)^827 := by
    have hnat : (2143469879 : ℕ)^1083*100000000000000^827 ≤ 32982050020957^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143469879 5000000000 32982050020957 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3720816487/10000000000 : ℝ)^1083 ≤ (13699294737569/50000000000000 : ℝ)^827 := by
    have hnat : (3720816487 : ℕ)^1083*50000000000000^827 ≤ 13699294737569^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3720816487 10000000000 13699294737569 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2465609363/5000000000 : ℝ)^1083 ≤ (9904840121611/25000000000000 : ℝ)^827 := by
    have hnat : (2465609363 : ℕ)^1083*25000000000000^827 ≤ 9904840121611^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465609363 5000000000 9904840121611 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143469879/5000000000 : ℝ), (3720816487/10000000000 : ℝ), (2465609363/5000000000 : ℝ)] ![(32982050020957/100000000000000 : ℝ), (13699294737569/50000000000000 : ℝ), (9904840121611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143469879/5000000000 : ℝ)|^1083 ≤ (32982050020957/100000000000000 : ℝ)^827
        have hw : |(2143469879/5000000000 : ℝ)|=(2143469879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3720816487/10000000000 : ℝ)|^1083 ≤ (13699294737569/50000000000000 : ℝ)^827
        have hw : |(3720816487/10000000000 : ℝ)|=(3720816487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2465609363/5000000000 : ℝ)|^1083 ≤ (9904840121611/25000000000000 : ℝ)^827
        have hw : |(2465609363/5000000000 : ℝ)|=(2465609363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s1_4 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-986260747/5000000000 : ℝ)*x 0 + (79133153/156250000 : ℝ)*x 1 + (1124361233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986260747/5000000000 : ℝ)^1083 ≤ (5967107979263/50000000000000 : ℝ)^827 := by
    have hnat : (986260747 : ℕ)^1083*50000000000000^827 ≤ 5967107979263^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986260747 5000000000 5967107979263 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79133153/156250000 : ℝ)^1083 ≤ (41027735919387/100000000000000 : ℝ)^827 := by
    have hnat : (79133153 : ℕ)^1083*100000000000000^827 ≤ 41027735919387^827*156250000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79133153 156250000 41027735919387 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124361233/2000000000 : ℝ)^1083 ≤ (2939878006659/6250000000000 : ℝ)^827 := by
    have hnat : (1124361233 : ℕ)^1083*6250000000000^827 ≤ 2939878006659^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124361233 2000000000 2939878006659 6250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986260747/5000000000 : ℝ), (79133153/156250000 : ℝ), (1124361233/2000000000 : ℝ)] ![(5967107979263/50000000000000 : ℝ), (41027735919387/100000000000000 : ℝ), (2939878006659/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986260747/5000000000 : ℝ)|^1083 ≤ (5967107979263/50000000000000 : ℝ)^827
        have hw : |(-986260747/5000000000 : ℝ)|=(986260747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79133153/156250000 : ℝ)|^1083 ≤ (41027735919387/100000000000000 : ℝ)^827
        have hw : |(79133153/156250000 : ℝ)|=(79133153/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124361233/2000000000 : ℝ)|^1083 ≤ (2939878006659/6250000000000 : ℝ)^827
        have hw : |(1124361233/2000000000 : ℝ)|=(1124361233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s1_5 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (105079339/200000000 : ℝ)*x 0 + (-342380959/2000000000 : ℝ)*x 1 + (351362891/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105079339/200000000 : ℝ)^1083 ≤ (8609807877661/20000000000000 : ℝ)^827 := by
    have hnat : (105079339 : ℕ)^1083*20000000000000^827 ≤ 8609807877661^827*200000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105079339 200000000 8609807877661 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342380959/2000000000 : ℝ)^1083 ≤ (9912911487783/100000000000000 : ℝ)^827 := by
    have hnat : (342380959 : ℕ)^1083*100000000000000^827 ≤ 9912911487783^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342380959 2000000000 9912911487783 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351362891/625000000 : ℝ)^1083 ≤ (23519024551821/50000000000000 : ℝ)^827 := by
    have hnat : (351362891 : ℕ)^1083*50000000000000^827 ≤ 23519024551821^827*625000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351362891 625000000 23519024551821 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105079339/200000000 : ℝ), (-342380959/2000000000 : ℝ), (351362891/625000000 : ℝ)] ![(8609807877661/20000000000000 : ℝ), (9912911487783/100000000000000 : ℝ), (23519024551821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105079339/200000000 : ℝ)|^1083 ≤ (8609807877661/20000000000000 : ℝ)^827
        have hw : |(105079339/200000000 : ℝ)|=(105079339/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-342380959/2000000000 : ℝ)|^1083 ≤ (9912911487783/100000000000000 : ℝ)^827
        have hw : |(-342380959/2000000000 : ℝ)|=(342380959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(351362891/625000000 : ℝ)|^1083 ≤ (23519024551821/50000000000000 : ℝ)^827
        have hw : |(351362891/625000000 : ℝ)|=(351362891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s1_6 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1313491711/2500000000 : ℝ)*x 0 + (140545159/250000000 : ℝ)*x 1 + (-427976199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313491711/2500000000 : ℝ)^1083 ≤ (21524519125463/50000000000000 : ℝ)^827 := by
    have hnat : (1313491711 : ℕ)^1083*50000000000000^827 ≤ 21524519125463^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313491711 2500000000 21524519125463 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140545159/250000000 : ℝ)^1083 ≤ (23519025121591/50000000000000 : ℝ)^827 := by
    have hnat : (140545159 : ℕ)^1083*50000000000000^827 ≤ 23519025121591^827*250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140545159 250000000 23519025121591 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427976199/2500000000 : ℝ)^1083 ≤ (4956455747683/50000000000000 : ℝ)^827 := by
    have hnat : (427976199 : ℕ)^1083*50000000000000^827 ≤ 4956455747683^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427976199 2500000000 4956455747683 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313491711/2500000000 : ℝ), (140545159/250000000 : ℝ), (-427976199/2500000000 : ℝ)] ![(21524519125463/50000000000000 : ℝ), (23519025121591/50000000000000 : ℝ), (4956455747683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313491711/2500000000 : ℝ)|^1083 ≤ (21524519125463/50000000000000 : ℝ)^827
        have hw : |(1313491711/2500000000 : ℝ)|=(1313491711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140545159/250000000 : ℝ)|^1083 ≤ (23519025121591/50000000000000 : ℝ)^827
        have hw : |(140545159/250000000 : ℝ)|=(140545159/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427976199/2500000000 : ℝ)|^1083 ≤ (4956455747683/50000000000000 : ℝ)^827
        have hw : |(-427976199/2500000000 : ℝ)|=(427976199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s1_7 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4187467/9765625 : ℝ)*x 0 + (1229094873/2500000000 : ℝ)*x 1 + (373591801/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187467/9765625 : ℝ)^1083 ≤ (32992392082191/100000000000000 : ℝ)^827 := by
    have hnat : (4187467 : ℕ)^1083*100000000000000^827 ≤ 32992392082191^827*9765625^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187467 9765625 32992392082191 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1229094873/2500000000 : ℝ)^1083 ≤ (39463302801151/100000000000000 : ℝ)^827 := by
    have hnat : (1229094873 : ℕ)^1083*100000000000000^827 ≤ 39463302801151^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229094873 2500000000 39463302801151 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373591801/1000000000 : ℝ)^1083 ≤ (5508861020257/20000000000000 : ℝ)^827 := by
    have hnat : (373591801 : ℕ)^1083*20000000000000^827 ≤ 5508861020257^827*1000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373591801 1000000000 5508861020257 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187467/9765625 : ℝ), (1229094873/2500000000 : ℝ), (373591801/1000000000 : ℝ)] ![(32992392082191/100000000000000 : ℝ), (39463302801151/100000000000000 : ℝ), (5508861020257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187467/9765625 : ℝ)|^1083 ≤ (32992392082191/100000000000000 : ℝ)^827
        have hw : |(4187467/9765625 : ℝ)|=(4187467/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1229094873/2500000000 : ℝ)|^1083 ≤ (39463302801151/100000000000000 : ℝ)^827
        have hw : |(1229094873/2500000000 : ℝ)|=(1229094873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(373591801/1000000000 : ℝ)|^1083 ≤ (5508861020257/20000000000000 : ℝ)^827
        have hw : |(373591801/1000000000 : ℝ)|=(373591801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1372_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1637/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7163/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26657/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1637/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26657/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1637/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26657/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1637/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26657/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1637/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26657/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1637/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26657/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1637/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (1637/100000 : ℝ) ^ (4331/1024 : ℝ) ≤ (279468486091/10000000000000000000 : ℝ) := by
    have hpowers : (1637/100000 : ℝ)^4331 ≤ (279468486091/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1637 : ℕ)^4331*10000000000000000000^1024 ≤ 279468486091^1024*100000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1637 100000 279468486091 10000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1637/100000 : ℝ)) (X := (279468486091/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26657/100000 : ℝ) ^ (4331/1024 : ℝ) ≤ (186398865628053563/50000000000000000000 : ℝ) := by
    have hpowers : (26657/100000 : ℝ)^4331 ≤ (186398865628053563/50000000000000000000 : ℝ)^1024 := by
      have hnat : (26657 : ℕ)^4331*50000000000000000000^1024 ≤ 186398865628053563^1024*100000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26657 100000 186398865628053563 50000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26657/100000 : ℝ)) (X := (186398865628053563/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000279468486091/5000000000000000000 : ℝ) ≤ (10000000132152263/10000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (5000000279468486091/5000000000000000000 : ℝ)^1024 ≤ (10000000132152263/10000000000000000 : ℝ)^4331 := by
      have hnat : (5000000279468486091 : ℕ)^1024*10000000000000000^4331 ≤ 10000000132152263^4331*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000279468486091 5000000000000000000 10000000132152263 10000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000132152263/10000000000000000 : ℝ)) (X := (5000000279468486091/5000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25093200131485242009/25000000000000000000 : ℝ) ≤ (5004400895746787/5000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25093200131485242009/25000000000000000000 : ℝ)^1024 ≤ (5004400895746787/5000000000000000 : ℝ)^4331 := by
      have hnat : (25093200131485242009 : ℕ)^1024*5000000000000000^4331 ≤ 5004400895746787^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25093200131485242009 25000000000000000000 5004400895746787 5000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004400895746787/5000000000000000 : ℝ)) (X := (25093200131485242009/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25186398865628053563/25000000000000000000 : ℝ) ≤ (2003520690166977/2000000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25186398865628053563/25000000000000000000 : ℝ)^1024 ≤ (2003520690166977/2000000000000000 : ℝ)^4331 := by
      have hnat : (25186398865628053563 : ℕ)^1024*2000000000000000^4331 ≤ 2003520690166977^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25186398865628053563 25000000000000000000 2003520690166977 2000000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003520690166977/2000000000000000 : ℝ)) (X := (25186398865628053563/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(279468486091/10000000000000000000 : ℝ) ≤ ((125085593336883084023/125100000000000000000 : ℝ)+2*(8801659341311/2502000000000000 : ℝ)*(1637/100000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (125085593336883084023/125100000000000000000 : ℝ)+2*(8801659341311/2502000000000000 : ℝ)*(1637/100000 : ℝ)=(10000000132152263/10000000000000000 : ℝ) by norm_num, show 1+2*(279468486091/10000000000000000000 : ℝ)=(5000000279468486091/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(186398865628053563/50000000000000000000 : ℝ)+(279468486091/10000000000000000000 : ℝ) ≤ ((125085593336883084023/125100000000000000000 : ℝ)+(8801659341311/2502000000000000 : ℝ)*((26657/100000 : ℝ)+(1637/100000 : ℝ)))^(4331/1024 : ℝ) := by
    rw [show (125085593336883084023/125100000000000000000 : ℝ)+(8801659341311/2502000000000000 : ℝ)*((26657/100000 : ℝ)+(1637/100000 : ℝ))=(5004400895746787/5000000000000000 : ℝ) by norm_num, show 1+(186398865628053563/50000000000000000000 : ℝ)+(279468486091/10000000000000000000 : ℝ)=(25093200131485242009/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(186398865628053563/50000000000000000000 : ℝ) ≤ ((125085593336883084023/125100000000000000000 : ℝ)+2*(8801659341311/2502000000000000 : ℝ)*(26657/100000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (125085593336883084023/125100000000000000000 : ℝ)+2*(8801659341311/2502000000000000 : ℝ)*(26657/100000 : ℝ)=(2003520690166977/2000000000000000 : ℝ) by norm_num, show 1+2*(186398865628053563/50000000000000000000 : ℝ)=(25186398865628053563/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125085593336883084023/125100000000000000000 : ℝ)*(X 1 0+X 2 0)+(8801659341311/2502000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (1637/100000 : ℝ)) (hi := (26657/100000 : ℝ)) (c := (125085593336883084023/125100000000000000000 : ℝ)) (alpha := (8801659341311/2502000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125085593336883084023/125100000000000000000 : ℝ)*(X 0 1+X 2 1)+(8801659341311/2502000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (1637/100000 : ℝ)) (hi := (26657/100000 : ℝ)) (c := (125085593336883084023/125100000000000000000 : ℝ)) (alpha := (8801659341311/2502000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125085593336883084023/125100000000000000000 : ℝ)*(X 0 2+X 1 2)+(8801659341311/2502000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (1637/100000 : ℝ)) (hi := (26657/100000 : ℝ)) (c := (125085593336883084023/125100000000000000000 : ℝ)) (alpha := (8801659341311/2502000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-986018633/5000000000 : ℝ)*X 0 0+(2814468501/5000000000 : ℝ)*X 0 1+(2528757721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5402607969/10000000000 : ℝ)*X 1 0+(-2276194419/10000000000 : ℝ)*X 1 1+(5057516743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2701304223/5000000000 : ℝ)*X 2 0+(2528757819/5000000000 : ℝ)*X 2 1+(-569048803/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2143469879/5000000000 : ℝ)*X 0 0+(3720816487/10000000000 : ℝ)*X 0 1+(2465609363/5000000000 : ℝ)*X 0 2+(2143469879/5000000000 : ℝ)*X 1 0+(3720816487/10000000000 : ℝ)*X 1 1+(2465609363/5000000000 : ℝ)*X 1 2+(2143469879/5000000000 : ℝ)*X 2 0+(3720816487/10000000000 : ℝ)*X 2 1+(2465609363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-986260747/5000000000 : ℝ)*X 0 0+(79133153/156250000 : ℝ)*X 0 1+(1124361233/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105079339/200000000 : ℝ)*X 1 0+(-342380959/2000000000 : ℝ)*X 1 1+(351362891/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313491711/2500000000 : ℝ)*X 2 0+(140545159/250000000 : ℝ)*X 2 1+(-427976199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4187467/9765625 : ℝ)*X 0 0+(1229094873/2500000000 : ℝ)*X 0 1+(373591801/1000000000 : ℝ)*X 0 2+(4187467/9765625 : ℝ)*X 1 0+(1229094873/2500000000 : ℝ)*X 1 1+(373591801/1000000000 : ℝ)*X 1 2+(4187467/9765625 : ℝ)*X 2 0+(1229094873/2500000000 : ℝ)*X 2 1+(373591801/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1577966162645730031103111777/260625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4393609/10000000000000 : ℝ)*(base16) + (822144483/100000000000000 : ℝ)*(base19) + (1063245957/100000000000000 : ℝ)*(base23) + (23043899/100000000000000 : ℝ)*(upper2) + (73695221/50000000000000 : ℝ)*(upper3) + (1288108191426793/100000000000000 : ℝ)*(major0) + (1288108191426793/100000000000000 : ℝ)*(major1) + (644054095713397/50000000000000 : ℝ)*(major2) + (10937694803879/625000000000 : ℝ)*(sp0) + (875019266280683/50000000000000 : ℝ)*(sp1) + (875019167697991/50000000000000 : ℝ)*(sp2) + (103271721288253/12500000000000 : ℝ)*(sp3) + (82300213/1000000000000 : ℝ)*(sp4) + (1506043701/50000000000000 : ℝ)*(sp7) + (413088391196713/50000000000000 : ℝ)*(f.failure) + (87501969932097/5000000000000 : ℝ)*(f.sum) + (182834115786319/83400000000000000000000000000 : ℝ)*base65 + (89873506384700871761/12510000000000000000000000000000000 : ℝ)*base68 + (28143448120198331131/6255000000000000000000000000000000 : ℝ)*base69 + (8030222970800871761/12510000000000000000000000000000000 : ℝ)*base72 + (498405419363681/83400000000000000000000000000 : ℝ)*base74 + (64680694814908331131/6255000000000000000000000000000000 : ℝ)*base75 + (7721260098682140587/4170000000000000000000000000000000 : ℝ)*base78 + (3484399186042140587/4170000000000000000000000000000000 : ℝ)*base80 + (324086711919623/125100000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (57076229/5000000000000000000000 : ℝ)*base89 + (57076229/5000000000000000000000 : ℝ)*base91 + (7076229/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24813164922562288415473/3475000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72281247/100000000000000 : ℝ)*(base1) + (143913371/10000000000000 : ℝ)*(base19) + (1404587741/100000000000000 : ℝ)*(base23) + (42802753/25000000000000 : ℝ)*(upper3) + (79358471/50000000000000 : ℝ)*(upper5) + (330192796439407/25000000000000 : ℝ)*(major0) + (330192796439407/25000000000000 : ℝ)*(major1) + (330192796439407/25000000000000 : ℝ)*(major2) + (3850538297/50000000000000 : ℝ)*(sp1) + (3879803433/50000000000000 : ℝ)*(sp2) + (14018873279399/781250000000 : ℝ)*(sp4) + (11215041045447/625000000000 : ℝ)*(sp5) + (897203271643609/50000000000000 : ℝ)*(sp6) + (52945397108513/6250000000000 : ℝ)*(sp7) + (169425285203491/20000000000000 : ℝ)*(f.failure) + (71776628299273/4000000000000 : ℝ)*(f.sum) + (69048250700177/31275000000000000000000000000 : ℝ)*base65 + (1461599159112714787/1042500000000000000000000000000000 : ℝ)*base67 + (10771443618887285213/1042500000000000000000000000000000 : ℝ)*base70 + (820005384212285213/1042500000000000000000000000000000 : ℝ)*base72 + (157331653653827/31275000000000000000000000000 : ℝ)*base73 + (843983396877714787/1042500000000000000000000000000000 : ℝ)*base75 + (7882629656502714787/1042500000000000000000000000000000 : ℝ)*base77 + (5049242813357285213/1042500000000000000000000000000000 : ℝ)*base80 + (67093773868577/31275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (20158103/2000000000000000000000 : ℝ)*base89 + (20158103/2000000000000000000000 : ℝ)*base91 + (20158103/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1372_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26657/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1637/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1372_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1372_s2_0 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-200964731/1000000000 : ℝ)*x 0 + (341988597/625000000 : ℝ)*x 1 + (648812837/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200964731/1000000000 : ℝ)^1083 ≤ (12229220699499/100000000000000 : ℝ)^827 := by
    have hnat : (200964731 : ℕ)^1083*100000000000000^827 ≤ 12229220699499^827*1000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200964731 1000000000 12229220699499 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341988597/625000000 : ℝ)^1083 ≤ (22700716815567/50000000000000 : ℝ)^827 := by
    have hnat : (341988597 : ℕ)^1083*50000000000000^827 ≤ 22700716815567^827*625000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341988597 625000000 22700716815567 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648812837/1250000000 : ℝ)^1083 ≤ (21184672824747/50000000000000 : ℝ)^827 := by
    have hnat : (648812837 : ℕ)^1083*50000000000000^827 ≤ 21184672824747^827*1250000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648812837 1250000000 21184672824747 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200964731/1000000000 : ℝ), (341988597/625000000 : ℝ), (648812837/1250000000 : ℝ)] ![(12229220699499/100000000000000 : ℝ), (22700716815567/50000000000000 : ℝ), (21184672824747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200964731/1000000000 : ℝ)|^1083 ≤ (12229220699499/100000000000000 : ℝ)^827
        have hw : |(-200964731/1000000000 : ℝ)|=(200964731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341988597/625000000 : ℝ)|^1083 ≤ (22700716815567/50000000000000 : ℝ)^827
        have hw : |(341988597/625000000 : ℝ)|=(341988597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648812837/1250000000 : ℝ)|^1083 ≤ (21184672824747/50000000000000 : ℝ)^827
        have hw : |(648812837/1250000000 : ℝ)|=(648812837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s2_1 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5363879767/10000000000 : ℝ)*x 0 + (-2154774217/10000000000 : ℝ)*x 1 + (519050287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363879767/10000000000 : ℝ)^1083 ≤ (552902532631/1250000000000 : ℝ)^827 := by
    have hnat : (5363879767 : ℕ)^1083*1250000000000^827 ≤ 552902532631^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363879767 10000000000 552902532631 1250000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154774217/10000000000 : ℝ)^1083 ≤ (3349612464961/25000000000000 : ℝ)^827 := by
    have hnat : (2154774217 : ℕ)^1083*25000000000000^827 ≤ 3349612464961^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154774217 10000000000 3349612464961 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519050287/1000000000 : ℝ)^1083 ≤ (42369347509501/100000000000000 : ℝ)^827 := by
    have hnat : (519050287 : ℕ)^1083*100000000000000^827 ≤ 42369347509501^827*1000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519050287 1000000000 42369347509501 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363879767/10000000000 : ℝ), (-2154774217/10000000000 : ℝ), (519050287/1000000000 : ℝ)] ![(552902532631/1250000000000 : ℝ), (3349612464961/25000000000000 : ℝ), (42369347509501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363879767/10000000000 : ℝ)|^1083 ≤ (552902532631/1250000000000 : ℝ)^827
        have hw : |(5363879767/10000000000 : ℝ)|=(5363879767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2154774217/10000000000 : ℝ)|^1083 ≤ (3349612464961/25000000000000 : ℝ)^827
        have hw : |(-2154774217/10000000000 : ℝ)|=(2154774217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519050287/1000000000 : ℝ)|^1083 ≤ (42369347509501/100000000000000 : ℝ)^827
        have hw : |(519050287/1000000000 : ℝ)|=(519050287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s2_2 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1072775949/2000000000 : ℝ)*x 0 + (5190502879/10000000000 : ℝ)*x 1 + (-430954847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072775949/2000000000 : ℝ)^1083 ≤ (22116101186451/50000000000000 : ℝ)^827 := by
    have hnat : (1072775949 : ℕ)^1083*50000000000000^827 ≤ 22116101186451^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072775949 2000000000 22116101186451 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190502879/10000000000 : ℝ)^1083 ≤ (10592336901427/25000000000000 : ℝ)^827 := by
    have hnat : (5190502879 : ℕ)^1083*25000000000000^827 ≤ 10592336901427^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190502879 10000000000 10592336901427 25000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430954847/2000000000 : ℝ)^1083 ≤ (2679690001283/20000000000000 : ℝ)^827 := by
    have hnat : (430954847 : ℕ)^1083*20000000000000^827 ≤ 2679690001283^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430954847 2000000000 2679690001283 20000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072775949/2000000000 : ℝ), (5190502879/10000000000 : ℝ), (-430954847/2000000000 : ℝ)] ![(22116101186451/50000000000000 : ℝ), (10592336901427/25000000000000 : ℝ), (2679690001283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072775949/2000000000 : ℝ)|^1083 ≤ (22116101186451/50000000000000 : ℝ)^827
        have hw : |(1072775949/2000000000 : ℝ)|=(1072775949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190502879/10000000000 : ℝ)|^1083 ≤ (10592336901427/25000000000000 : ℝ)^827
        have hw : |(5190502879/10000000000 : ℝ)|=(5190502879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430954847/2000000000 : ℝ)|^1083 ≤ (2679690001283/20000000000000 : ℝ)^827
        have hw : |(-430954847/2000000000 : ℝ)|=(430954847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s2_3 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (862665889/2000000000 : ℝ)*x 0 + (2012425709/5000000000 : ℝ)*x 1 + (2310371461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862665889/2000000000 : ℝ)^1083 ≤ (33248184079087/100000000000000 : ℝ)^827 := by
    have hnat : (862665889 : ℕ)^1083*100000000000000^827 ≤ 33248184079087^827*2000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862665889 2000000000 33248184079087 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012425709/5000000000 : ℝ)^1083 ≤ (759170196961/2500000000000 : ℝ)^827 := by
    have hnat : (2012425709 : ℕ)^1083*2500000000000^827 ≤ 759170196961^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012425709 5000000000 759170196961 2500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2310371461/5000000000 : ℝ)^1083 ≤ (18192504015157/50000000000000 : ℝ)^827 := by
    have hnat : (2310371461 : ℕ)^1083*50000000000000^827 ≤ 18192504015157^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310371461 5000000000 18192504015157 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862665889/2000000000 : ℝ), (2012425709/5000000000 : ℝ), (2310371461/5000000000 : ℝ)] ![(33248184079087/100000000000000 : ℝ), (759170196961/2500000000000 : ℝ), (18192504015157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862665889/2000000000 : ℝ)|^1083 ≤ (33248184079087/100000000000000 : ℝ)^827
        have hw : |(862665889/2000000000 : ℝ)|=(862665889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012425709/5000000000 : ℝ)|^1083 ≤ (759170196961/2500000000000 : ℝ)^827
        have hw : |(2012425709/5000000000 : ℝ)|=(2012425709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2310371461/5000000000 : ℝ)|^1083 ≤ (18192504015157/50000000000000 : ℝ)^827
        have hw : |(2310371461/5000000000 : ℝ)|=(2310371461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s2_4 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-502426291/2500000000 : ℝ)*x 0 + (1298052601/2500000000 : ℝ)*x 1 + (5470094919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502426291/2500000000 : ℝ)^1083 ≤ (12229681738017/100000000000000 : ℝ)^827 := by
    have hnat : (502426291 : ℕ)^1083*100000000000000^827 ≤ 12229681738017^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502426291 2500000000 12229681738017 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298052601/2500000000 : ℝ)^1083 ≤ (5298450181921/12500000000000 : ℝ)^827 := by
    have hnat : (1298052601 : ℕ)^1083*12500000000000^827 ≤ 5298450181921^827*2500000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298052601 2500000000 5298450181921 12500000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470094919/10000000000 : ℝ)^1083 ≤ (45382716792139/100000000000000 : ℝ)^827 := by
    have hnat : (5470094919 : ℕ)^1083*100000000000000^827 ≤ 45382716792139^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470094919 10000000000 45382716792139 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502426291/2500000000 : ℝ), (1298052601/2500000000 : ℝ), (5470094919/10000000000 : ℝ)] ![(12229681738017/100000000000000 : ℝ), (5298450181921/12500000000000 : ℝ), (45382716792139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502426291/2500000000 : ℝ)|^1083 ≤ (12229681738017/100000000000000 : ℝ)^827
        have hw : |(-502426291/2500000000 : ℝ)|=(502426291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298052601/2500000000 : ℝ)|^1083 ≤ (5298450181921/12500000000000 : ℝ)^827
        have hw : |(1298052601/2500000000 : ℝ)|=(1298052601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470094919/10000000000 : ℝ)|^1083 ≤ (45382716792139/100000000000000 : ℝ)^827
        have hw : |(5470094919/10000000000 : ℝ)|=(5470094919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s2_5 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5291139859/10000000000 : ℝ)*x 0 + (-937590961/5000000000 : ℝ)*x 1 + (109401897/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291139859/10000000000 : ℝ)^1083 ≤ (868966803711/2000000000000 : ℝ)^827 := by
    have hnat : (5291139859 : ℕ)^1083*2000000000000^827 ≤ 868966803711^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291139859 10000000000 868966803711 2000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (937590961/5000000000 : ℝ)^1083 ≤ (5584471883099/50000000000000 : ℝ)^827 := by
    have hnat : (937590961 : ℕ)^1083*50000000000000^827 ≤ 5584471883099^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937590961 5000000000 5584471883099 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109401897/200000000 : ℝ)^1083 ≤ (22691358021237/50000000000000 : ℝ)^827 := by
    have hnat : (109401897 : ℕ)^1083*50000000000000^827 ≤ 22691358021237^827*200000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109401897 200000000 22691358021237 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291139859/10000000000 : ℝ), (-937590961/5000000000 : ℝ), (109401897/200000000 : ℝ)] ![(868966803711/2000000000000 : ℝ), (5584471883099/50000000000000 : ℝ), (22691358021237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291139859/10000000000 : ℝ)|^1083 ≤ (868966803711/2000000000000 : ℝ)^827
        have hw : |(5291139859/10000000000 : ℝ)|=(5291139859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-937590961/5000000000 : ℝ)|^1083 ≤ (5584471883099/50000000000000 : ℝ)^827
        have hw : |(-937590961/5000000000 : ℝ)|=(937590961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109401897/200000000 : ℝ)|^1083 ≤ (22691358021237/50000000000000 : ℝ)^827
        have hw : |(109401897/200000000 : ℝ)|=(109401897/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s2_6 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2645569903/5000000000 : ℝ)*x 0 + (5470094919/10000000000 : ℝ)*x 1 + (-937590949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645569903/5000000000 : ℝ)^1083 ≤ (43448339615619/100000000000000 : ℝ)^827 := by
    have hnat : (2645569903 : ℕ)^1083*100000000000000^827 ≤ 43448339615619^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645569903 5000000000 43448339615619 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470094919/10000000000 : ℝ)^1083 ≤ (45382716792139/100000000000000 : ℝ)^827 := by
    have hnat : (5470094919 : ℕ)^1083*100000000000000^827 ≤ 45382716792139^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470094919 10000000000 45382716792139 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937590949/5000000000 : ℝ)^1083 ≤ (11168943578999/100000000000000 : ℝ)^827 := by
    have hnat : (937590949 : ℕ)^1083*100000000000000^827 ≤ 11168943578999^827*5000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937590949 5000000000 11168943578999 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645569903/5000000000 : ℝ), (5470094919/10000000000 : ℝ), (-937590949/5000000000 : ℝ)] ![(43448339615619/100000000000000 : ℝ), (45382716792139/100000000000000 : ℝ), (11168943578999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645569903/5000000000 : ℝ)|^1083 ≤ (43448339615619/100000000000000 : ℝ)^827
        have hw : |(2645569903/5000000000 : ℝ)|=(2645569903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470094919/10000000000 : ℝ)|^1083 ≤ (45382716792139/100000000000000 : ℝ)^827
        have hw : |(5470094919/10000000000 : ℝ)|=(5470094919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937590949/5000000000 : ℝ)|^1083 ≤ (11168943578999/100000000000000 : ℝ)^827
        have hw : |(-937590949/5000000000 : ℝ)|=(937590949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1372_s2_7 (p : ℝ) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4313452153/10000000000 : ℝ)*x 0 + (461712597/1000000000 : ℝ)*x 1 + (402849997/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313452153/10000000000 : ℝ)^1083 ≤ (33249422741723/100000000000000 : ℝ)^827 := by
    have hnat : (4313452153 : ℕ)^1083*100000000000000^827 ≤ 33249422741723^827*10000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313452153 10000000000 33249422741723 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461712597/1000000000 : ℝ)^1083 ≤ (36347715338543/100000000000000 : ℝ)^827 := by
    have hnat : (461712597 : ℕ)^1083*100000000000000^827 ≤ 36347715338543^827*1000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461712597 1000000000 36347715338543 100000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402849997/1000000000 : ℝ)^1083 ≤ (15201430949151/50000000000000 : ℝ)^827 := by
    have hnat : (402849997 : ℕ)^1083*50000000000000^827 ≤ 15201430949151^827*1000000000^1083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402849997 1000000000 15201430949151 50000000000000 1083 827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1083/256 : ℝ)) 1083 827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313452153/10000000000 : ℝ), (461712597/1000000000 : ℝ), (402849997/1000000000 : ℝ)] ![(33249422741723/100000000000000 : ℝ), (36347715338543/100000000000000 : ℝ), (15201430949151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313452153/10000000000 : ℝ)|^1083 ≤ (33249422741723/100000000000000 : ℝ)^827
        have hw : |(4313452153/10000000000 : ℝ)|=(4313452153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(461712597/1000000000 : ℝ)|^1083 ≤ (36347715338543/100000000000000 : ℝ)^827
        have hw : |(461712597/1000000000 : ℝ)|=(461712597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(402849997/1000000000 : ℝ)|^1083 ≤ (15201430949151/50000000000000 : ℝ)^827
        have hw : |(402849997/1000000000 : ℝ)|=(402849997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1372_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5021/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1599/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7163/100000 : ℝ) ^ (4331/1024 : ℝ) ≤ (1437583370977899/100000000000000000000 : ℝ) := by
    have hpowers : (7163/100000 : ℝ)^4331 ≤ (1437583370977899/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7163 : ℕ)^4331*100000000000000000000^1024 ≤ 1437583370977899^1024*100000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7163 100000 1437583370977899 100000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7163/100000 : ℝ)) (X := (1437583370977899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19241/100000 : ℝ) ^ (4331/1024 : ℝ) ≤ (46947924551250503/50000000000000000000 : ℝ) := by
    have hpowers : (19241/100000 : ℝ)^4331 ≤ (46947924551250503/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19241 : ℕ)^4331*50000000000000000000^1024 ≤ 46947924551250503^1024*100000^4331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19241 100000 46947924551250503 50000000000000000000 4331 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19241/100000 : ℝ)) (X := (46947924551250503/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001437583370977899/50000000000000000000 : ℝ) ≤ (400002719130387/400000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (50001437583370977899/50000000000000000000 : ℝ)^1024 ≤ (400002719130387/400000000000000 : ℝ)^4331 := by
      have hnat : (50001437583370977899 : ℕ)^1024*400000000000000^4331 ≤ 400002719130387^4331*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001437583370977899 50000000000000000000 400002719130387 400000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400002719130387/400000000000000 : ℝ)) (X := (50001437583370977899/50000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20019066686494695781/20000000000000000000 : ℝ) ≤ (200045063922343/200000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (20019066686494695781/20000000000000000000 : ℝ)^1024 ≤ (200045063922343/200000000000000 : ℝ)^4331 := by
      have hnat : (20019066686494695781 : ℕ)^1024*200000000000000^4331 ≤ 200045063922343^4331*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20019066686494695781 20000000000000000000 200045063922343 200000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200045063922343/200000000000000 : ℝ)) (X := (20019066686494695781/20000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25046947924551250503/25000000000000000000 : ℝ) ≤ (80035507311797/80000000000000 : ℝ) ^ (4331/1024 : ℝ) := by
    have hpowers : (25046947924551250503/25000000000000000000 : ℝ)^1024 ≤ (80035507311797/80000000000000 : ℝ)^4331 := by
      have hnat : (25046947924551250503 : ℕ)^1024*80000000000000^4331 ≤ 80035507311797^4331*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25046947924551250503 25000000000000000000 80035507311797 80000000000000 1024 4331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80035507311797/80000000000000 : ℝ)) (X := (25046947924551250503/25000000000000000000 : ℝ)) (by norm_num) 4331 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1437583370977899/100000000000000000000 : ℝ) ≤ ((603747578051970839/603900000000000000 : ℝ)+2*(87408714299/48312000000000 : ℝ)*(7163/100000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (603747578051970839/603900000000000000 : ℝ)+2*(87408714299/48312000000000 : ℝ)*(7163/100000 : ℝ)=(400002719130387/400000000000000 : ℝ) by norm_num, show 1+2*(1437583370977899/100000000000000000000 : ℝ)=(50001437583370977899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46947924551250503/50000000000000000000 : ℝ)+(1437583370977899/100000000000000000000 : ℝ) ≤ ((603747578051970839/603900000000000000 : ℝ)+(87408714299/48312000000000 : ℝ)*((19241/100000 : ℝ)+(7163/100000 : ℝ)))^(4331/1024 : ℝ) := by
    rw [show (603747578051970839/603900000000000000 : ℝ)+(87408714299/48312000000000 : ℝ)*((19241/100000 : ℝ)+(7163/100000 : ℝ))=(200045063922343/200000000000000 : ℝ) by norm_num, show 1+(46947924551250503/50000000000000000000 : ℝ)+(1437583370977899/100000000000000000000 : ℝ)=(20019066686494695781/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46947924551250503/50000000000000000000 : ℝ) ≤ ((603747578051970839/603900000000000000 : ℝ)+2*(87408714299/48312000000000 : ℝ)*(19241/100000 : ℝ))^(4331/1024 : ℝ) := by
    rw [show (603747578051970839/603900000000000000 : ℝ)+2*(87408714299/48312000000000 : ℝ)*(19241/100000 : ℝ)=(80035507311797/80000000000000 : ℝ) by norm_num, show 1+2*(46947924551250503/50000000000000000000 : ℝ)=(25046947924551250503/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (603747578051970839/603900000000000000 : ℝ)*(X 1 0+X 2 0)+(87408714299/48312000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (7163/100000 : ℝ)) (hi := (19241/100000 : ℝ)) (c := (603747578051970839/603900000000000000 : ℝ)) (alpha := (87408714299/48312000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (603747578051970839/603900000000000000 : ℝ)*(X 0 1+X 2 1)+(87408714299/48312000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (7163/100000 : ℝ)) (hi := (19241/100000 : ℝ)) (c := (603747578051970839/603900000000000000 : ℝ)) (alpha := (87408714299/48312000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (603747578051970839/603900000000000000 : ℝ)*(X 0 2+X 1 2)+(87408714299/48312000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4331/1024 : ℝ)) (lo := (7163/100000 : ℝ)) (hi := (19241/100000 : ℝ)) (c := (603747578051970839/603900000000000000 : ℝ)) (alpha := (87408714299/48312000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-200964731/1000000000 : ℝ)*X 0 0+(341988597/625000000 : ℝ)*X 0 1+(648812837/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363879767/10000000000 : ℝ)*X 1 0+(-2154774217/10000000000 : ℝ)*X 1 1+(519050287/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072775949/2000000000 : ℝ)*X 2 0+(5190502879/10000000000 : ℝ)*X 2 1+(-430954847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862665889/2000000000 : ℝ)*X 0 0+(2012425709/5000000000 : ℝ)*X 0 1+(2310371461/5000000000 : ℝ)*X 0 2+(862665889/2000000000 : ℝ)*X 1 0+(2012425709/5000000000 : ℝ)*X 1 1+(2310371461/5000000000 : ℝ)*X 1 2+(862665889/2000000000 : ℝ)*X 2 0+(2012425709/5000000000 : ℝ)*X 2 1+(2310371461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-502426291/2500000000 : ℝ)*X 0 0+(1298052601/2500000000 : ℝ)*X 0 1+(5470094919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291139859/10000000000 : ℝ)*X 1 0+(-937590961/5000000000 : ℝ)*X 1 1+(109401897/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645569903/5000000000 : ℝ)*X 2 0+(5470094919/10000000000 : ℝ)*X 2 1+(-937590949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313452153/10000000000 : ℝ)*X 0 0+(461712597/1000000000 : ℝ)*X 0 1+(402849997/1000000000 : ℝ)*X 0 2+(4313452153/10000000000 : ℝ)*X 1 0+(461712597/1000000000 : ℝ)*X 1 1+(402849997/1000000000 : ℝ)*X 1 2+(4313452153/10000000000 : ℝ)*X 2 0+(461712597/1000000000 : ℝ)*X 2 1+(402849997/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1372_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7658295602129143875068489/3355000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50185077/20000000000000 : ℝ)*(base19) + (56679711/25000000000000 : ℝ)*(base23) + (2581829/50000000000000 : ℝ)*(lower2) + (49291109/100000000000000 : ℝ)*(upper3) + (24913031/100000000000000 : ℝ)*(upper5) + (1308226790549223/50000000000000 : ℝ)*(major0) + (1308226790549223/50000000000000 : ℝ)*(major1) + (2616453581098447/100000000000000 : ℝ)*(major2) + (355474111062751/10000000000000 : ℝ)*(sp0) + (1777372812677743/50000000000000 : ℝ)*(sp1) + (888686412390507/25000000000000 : ℝ)*(sp2) + (419539851869567/25000000000000 : ℝ)*(sp3) + (4765653361/100000000000000 : ℝ)*(sp4) + (1802349363/100000000000000 : ℝ)*(sp7) + (104885075614227/6250000000000 : ℝ)*(f.failure) + (3554745876280871/100000000000000 : ℝ)*(f.sum) + (15703778781563/4831200000000000000000000000 : ℝ)*base65 + (44538746833329347/30195000000000000000000000000000 : ℝ)*base67 + (431493024933362033/60390000000000000000000000000000 : ℝ)*base69 + (1170959383955653/30195000000000000000000000000000 : ℝ)*base72 + (188221890116203/24156000000000000000000000000 : ℝ)*base73 + (780238927883972033/60390000000000000000000000000000 : ℝ)*base75 + (11308552371951733/3355000000000000000000000000000 : ℝ)*base77 + (47548102204933267/3355000000000000000000000000000 : ℝ)*base80 + (2838119105219/671000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6370791/625000000000000000000 : ℝ)*base89 + (6370791/625000000000000000000 : ℝ)*base91 + (120791/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26193913043746855177972099/5032500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231048677/20000000000000 : ℝ)*(base19) + (623329703/50000000000000 : ℝ)*(base23) + (944939/781250000000 : ℝ)*(upper3) + (12926169/25000000000000 : ℝ)*(lower4) + (20126313/25000000000000 : ℝ)*(upper5) + (1324371858719341/50000000000000 : ℝ)*(major0) + (1324371858719341/50000000000000 : ℝ)*(major1) + (1324371858719341/50000000000000 : ℝ)*(major2) + (13502950133/100000000000000 : ℝ)*(sp1) + (3916617593/25000000000000 : ℝ)*(sp2) + (899653888616417/25000000000000 : ℝ)*(sp4) + (899650224068037/25000000000000 : ℝ)*(sp5) + (359859864133589/10000000000000 : ℝ)*(sp6) + (84943585345667/5000000000000 : ℝ)*(sp7) + (84943585345667/5000000000000 : ℝ)*(f.failure) + (899653888616417/25000000000000 : ℝ)*(f.sum) + (9466713370457/6039000000000000000000000000 : ℝ)*base66 + (152151341088918467/10065000000000000000000000000000 : ℝ)*base68 + (84094740205218467/10065000000000000000000000000000 : ℝ)*base70 + (15594188464166533/10065000000000000000000000000000 : ℝ)*base71 + (23875473961021/3019500000000000000000000000 : ℝ)*base74 + (1559631504611533/10065000000000000000000000000000 : ℝ)*base75 + (71023654917738467/10065000000000000000000000000000 : ℝ)*base78 + (100267615060608467/10065000000000000000000000000000 : ℝ)*base80 + (1279181126711/1207800000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (5144311/500000000000000000000 : ℝ)*base89 + (5144311/500000000000000000000 : ℝ)*base91 + (5144311/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1372_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1599/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1372_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1372_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1599/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1372_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1372_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1372_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4331/1024 : ℝ) ≤ p) (hpb : p ≤ (1083/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155911933/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1599/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1372_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
