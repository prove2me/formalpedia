-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1348_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:39.849265+00:00
-- url     : https://prove2.me/submissions/3b5035e8-0eb4-4647-b695-c71a97aeab81

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
theorem support_rectangle_w1348_s0_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-902802273/5000000000 : ℝ)*x 0 + (5994329297/10000000000 : ℝ)*x 1 + (2406169317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (902802273/5000000000 : ℝ)^1077 ≤ (5294153586683/50000000000000 : ℝ)^821 := by
    have hnat : (902802273 : ℕ)^1077*50000000000000^821 ≤ 5294153586683^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902802273 5000000000 5294153586683 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5994329297/10000000000 : ℝ)^1077 ≤ (51101872322499/100000000000000 : ℝ)^821 := by
    have hnat : (5994329297 : ℕ)^1077*100000000000000^821 ≤ 51101872322499^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5994329297 10000000000 51101872322499 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2406169317/5000000000 : ℝ)^1077 ≤ (1532392819321/4000000000000 : ℝ)^821 := by
    have hnat : (2406169317 : ℕ)^1077*4000000000000^821 ≤ 1532392819321^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406169317 5000000000 1532392819321 4000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-902802273/5000000000 : ℝ), (5994329297/10000000000 : ℝ), (2406169317/5000000000 : ℝ)] ![(5294153586683/50000000000000 : ℝ), (51101872322499/100000000000000 : ℝ), (1532392819321/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-902802273/5000000000 : ℝ)|^1077 ≤ (5294153586683/50000000000000 : ℝ)^821
        have hw : |(-902802273/5000000000 : ℝ)|=(902802273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5994329297/10000000000 : ℝ)|^1077 ≤ (51101872322499/100000000000000 : ℝ)^821
        have hw : |(5994329297/10000000000 : ℝ)|=(5994329297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2406169317/5000000000 : ℝ)|^1077 ≤ (1532392819321/4000000000000 : ℝ)^821
        have hw : |(2406169317/5000000000 : ℝ)|=(2406169317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s0_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1100228153/2000000000 : ℝ)*x 0 + (-1238575091/5000000000 : ℝ)*x 1 + (481233907/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100228153/2000000000 : ℝ)^1077 ≤ (5707318168643/12500000000000 : ℝ)^821 := by
    have hnat : (1100228153 : ℕ)^1077*12500000000000^821 ≤ 5707318168643^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100228153 2000000000 5707318168643 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238575091/5000000000 : ℝ)^1077 ≤ (16031629602033/100000000000000 : ℝ)^821 := by
    have hnat : (1238575091 : ℕ)^1077*100000000000000^821 ≤ 16031629602033^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238575091 5000000000 16031629602033 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481233907/1000000000 : ℝ)^1077 ≤ (19154912518093/50000000000000 : ℝ)^821 := by
    have hnat : (481233907 : ℕ)^1077*50000000000000^821 ≤ 19154912518093^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481233907 1000000000 19154912518093 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100228153/2000000000 : ℝ), (-1238575091/5000000000 : ℝ), (481233907/1000000000 : ℝ)] ![(5707318168643/12500000000000 : ℝ), (16031629602033/100000000000000 : ℝ), (19154912518093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100228153/2000000000 : ℝ)|^1077 ≤ (5707318168643/12500000000000 : ℝ)^821
        have hw : |(1100228153/2000000000 : ℝ)|=(1100228153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1238575091/5000000000 : ℝ)|^1077 ≤ (16031629602033/100000000000000 : ℝ)^821
        have hw : |(-1238575091/5000000000 : ℝ)|=(1238575091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481233907/1000000000 : ℝ)|^1077 ≤ (19154912518093/50000000000000 : ℝ)^821
        have hw : |(481233907/1000000000 : ℝ)|=(481233907/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s0_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2750570269/5000000000 : ℝ)*x 0 + (1203084691/2500000000 : ℝ)*x 1 + (-49543017/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750570269/5000000000 : ℝ)^1077 ≤ (11414635719401/25000000000000 : ℝ)^821 := by
    have hnat : (2750570269 : ℕ)^1077*25000000000000^821 ≤ 11414635719401^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750570269 5000000000 11414635719401 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203084691/2500000000 : ℝ)^1077 ≤ (38309821840619/100000000000000 : ℝ)^821 := by
    have hnat : (1203084691 : ℕ)^1077*100000000000000^821 ≤ 38309821840619^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203084691 2500000000 38309821840619 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49543017/200000000 : ℝ)^1077 ≤ (641265410929/4000000000000 : ℝ)^821 := by
    have hnat : (49543017 : ℕ)^1077*4000000000000^821 ≤ 641265410929^821*200000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49543017 200000000 641265410929 4000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750570269/5000000000 : ℝ), (1203084691/2500000000 : ℝ), (-49543017/200000000 : ℝ)] ![(11414635719401/25000000000000 : ℝ), (38309821840619/100000000000000 : ℝ), (641265410929/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750570269/5000000000 : ℝ)|^1077 ≤ (11414635719401/25000000000000 : ℝ)^821
        have hw : |(2750570269/5000000000 : ℝ)|=(2750570269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203084691/2500000000 : ℝ)|^1077 ≤ (38309821840619/100000000000000 : ℝ)^821
        have hw : |(1203084691/2500000000 : ℝ)|=(1203084691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49543017/200000000 : ℝ)|^1077 ≤ (641265410929/4000000000000 : ℝ)^821
        have hw : |(-49543017/200000000 : ℝ)|=(49543017/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s0_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2088924961/5000000000 : ℝ)*x 0 + (3106273323/10000000000 : ℝ)*x 1 + (223505103/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088924961/5000000000 : ℝ)^1077 ≤ (15912202637139/50000000000000 : ℝ)^821 := by
    have hnat : (2088924961 : ℕ)^1077*50000000000000^821 ≤ 15912202637139^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088924961 5000000000 15912202637139 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3106273323/10000000000 : ℝ)^1077 ≤ (21573094694097/100000000000000 : ℝ)^821 := by
    have hnat : (3106273323 : ℕ)^1077*100000000000000^821 ≤ 21573094694097^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106273323 10000000000 21573094694097 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223505103/400000000 : ℝ)^1077 ≤ (46602500014717/100000000000000 : ℝ)^821 := by
    have hnat : (223505103 : ℕ)^1077*100000000000000^821 ≤ 46602500014717^821*400000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223505103 400000000 46602500014717 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088924961/5000000000 : ℝ), (3106273323/10000000000 : ℝ), (223505103/400000000 : ℝ)] ![(15912202637139/50000000000000 : ℝ), (21573094694097/100000000000000 : ℝ), (46602500014717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088924961/5000000000 : ℝ)|^1077 ≤ (15912202637139/50000000000000 : ℝ)^821
        have hw : |(2088924961/5000000000 : ℝ)|=(2088924961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3106273323/10000000000 : ℝ)|^1077 ≤ (21573094694097/100000000000000 : ℝ)^821
        have hw : |(3106273323/10000000000 : ℝ)|=(3106273323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(223505103/400000000 : ℝ)|^1077 ≤ (46602500014717/100000000000000 : ℝ)^821
        have hw : |(223505103/400000000 : ℝ)|=(223505103/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s0_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-905014887/5000000000 : ℝ)*x 0 + (2421374689/5000000000 : ℝ)*x 1 + (745354071/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905014887/5000000000 : ℝ)^1077 ≤ (2655590485037/25000000000000 : ℝ)^821 := by
    have hnat : (905014887 : ℕ)^1077*25000000000000^821 ≤ 2655590485037^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905014887 5000000000 2655590485037 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2421374689/5000000000 : ℝ)^1077 ≤ (4828464150131/12500000000000 : ℝ)^821 := by
    have hnat : (2421374689 : ℕ)^1077*12500000000000^821 ≤ 4828464150131^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421374689 5000000000 4828464150131 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745354071/1250000000 : ℝ)^1077 ≤ (5074992483923/10000000000000 : ℝ)^821 := by
    have hnat : (745354071 : ℕ)^1077*10000000000000^821 ≤ 5074992483923^821*1250000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745354071 1250000000 5074992483923 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905014887/5000000000 : ℝ), (2421374689/5000000000 : ℝ), (745354071/1250000000 : ℝ)] ![(2655590485037/25000000000000 : ℝ), (4828464150131/12500000000000 : ℝ), (5074992483923/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905014887/5000000000 : ℝ)|^1077 ≤ (2655590485037/25000000000000 : ℝ)^821
        have hw : |(-905014887/5000000000 : ℝ)|=(905014887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2421374689/5000000000 : ℝ)|^1077 ≤ (4828464150131/12500000000000 : ℝ)^821
        have hw : |(2421374689/5000000000 : ℝ)|=(2421374689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(745354071/1250000000 : ℝ)|^1077 ≤ (5074992483923/10000000000000 : ℝ)^821
        have hw : |(745354071/1250000000 : ℝ)|=(745354071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s0_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2589485947/5000000000 : ℝ)*x 0 + (-1326657787/10000000000 : ℝ)*x 1 + (298141613/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589485947/5000000000 : ℝ)^1077 ≤ (2636455621053/6250000000000 : ℝ)^821 := by
    have hnat : (2589485947 : ℕ)^1077*6250000000000^821 ≤ 2636455621053^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589485947 5000000000 2636455621053 6250000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1326657787/10000000000 : ℝ)^1077 ≤ (1766697163447/25000000000000 : ℝ)^821 := by
    have hnat : (1326657787 : ℕ)^1077*25000000000000^821 ≤ 1766697163447^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326657787 10000000000 1766697163447 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298141613/500000000 : ℝ)^1077 ≤ (50749921400437/100000000000000 : ℝ)^821 := by
    have hnat : (298141613 : ℕ)^1077*100000000000000^821 ≤ 50749921400437^821*500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298141613 500000000 50749921400437 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589485947/5000000000 : ℝ), (-1326657787/10000000000 : ℝ), (298141613/500000000 : ℝ)] ![(2636455621053/6250000000000 : ℝ), (1766697163447/25000000000000 : ℝ), (50749921400437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589485947/5000000000 : ℝ)|^1077 ≤ (2636455621053/6250000000000 : ℝ)^821
        have hw : |(2589485947/5000000000 : ℝ)|=(2589485947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1326657787/10000000000 : ℝ)|^1077 ≤ (1766697163447/25000000000000 : ℝ)^821
        have hw : |(-1326657787/10000000000 : ℝ)|=(1326657787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298141613/500000000 : ℝ)|^1077 ≤ (50749921400437/100000000000000 : ℝ)^821
        have hw : |(298141613/500000000 : ℝ)|=(298141613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s0_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5178971853/10000000000 : ℝ)*x 0 + (2981416299/5000000000 : ℝ)*x 1 + (-1326657309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178971853/10000000000 : ℝ)^1077 ≤ (2636455593673/6250000000000 : ℝ)^821 := by
    have hnat : (5178971853 : ℕ)^1077*6250000000000^821 ≤ 2636455593673^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178971853 10000000000 2636455593673 6250000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981416299/5000000000 : ℝ)^1077 ≤ (50749925174177/100000000000000 : ℝ)^821 := by
    have hnat : (2981416299 : ℕ)^1077*100000000000000^821 ≤ 50749925174177^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981416299 5000000000 50749925174177 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1326657309/10000000000 : ℝ)^1077 ≤ (883348164207/12500000000000 : ℝ)^821 := by
    have hnat : (1326657309 : ℕ)^1077*12500000000000^821 ≤ 883348164207^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326657309 10000000000 883348164207 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178971853/10000000000 : ℝ), (2981416299/5000000000 : ℝ), (-1326657309/10000000000 : ℝ)] ![(2636455593673/6250000000000 : ℝ), (50749925174177/100000000000000 : ℝ), (883348164207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178971853/10000000000 : ℝ)|^1077 ≤ (2636455593673/6250000000000 : ℝ)^821
        have hw : |(5178971853/10000000000 : ℝ)|=(5178971853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2981416299/5000000000 : ℝ)|^1077 ≤ (50749925174177/100000000000000 : ℝ)^821
        have hw : |(2981416299/5000000000 : ℝ)|=(2981416299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1326657309/10000000000 : ℝ)|^1077 ≤ (883348164207/12500000000000 : ℝ)^821
        have hw : |(-1326657309/10000000000 : ℝ)|=(1326657309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s0_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4187137441/10000000000 : ℝ)*x 0 + (2761893641/5000000000 : ℝ)*x 1 + (3172393963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187137441/10000000000 : ℝ)^1077 ≤ (7979311051867/25000000000000 : ℝ)^821 := by
    have hnat : (4187137441 : ℕ)^1077*25000000000000^821 ≤ 7979311051867^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187137441 10000000000 7979311051867 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761893641/5000000000 : ℝ)^1077 ≤ (22952637591191/50000000000000 : ℝ)^821 := by
    have hnat : (2761893641 : ℕ)^1077*50000000000000^821 ≤ 22952637591191^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761893641 5000000000 22952637591191 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3172393963/10000000000 : ℝ)^1077 ≤ (443549611763/2000000000000 : ℝ)^821 := by
    have hnat : (3172393963 : ℕ)^1077*2000000000000^821 ≤ 443549611763^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172393963 10000000000 443549611763 2000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187137441/10000000000 : ℝ), (2761893641/5000000000 : ℝ), (3172393963/10000000000 : ℝ)] ![(7979311051867/25000000000000 : ℝ), (22952637591191/50000000000000 : ℝ), (443549611763/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187137441/10000000000 : ℝ)|^1077 ≤ (7979311051867/25000000000000 : ℝ)^821
        have hw : |(4187137441/10000000000 : ℝ)|=(4187137441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2761893641/5000000000 : ℝ)|^1077 ≤ (22952637591191/50000000000000 : ℝ)^821
        have hw : |(2761893641/5000000000 : ℝ)|=(2761893641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3172393963/10000000000 : ℝ)|^1077 ≤ (443549611763/2000000000000 : ℝ)^821
        have hw : |(3172393963/10000000000 : ℝ)|=(3172393963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1459/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6707/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4307/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4307 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4307*1^1024 ≤ 0^1024*1^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4307/1024 : ℝ) ≤ (1059772304014508409/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4307 ≤ (1059772304014508409/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4307*50000000000000000000^1024 ≤ 1059772304014508409^1024*5^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1059772304014508409 50000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1059772304014508409/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4307 := by
      have hnat : (1 : ℕ)^1024*1^4307 ≤ 1^4307*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51059772304014508409/50000000000000000000 : ℝ) ≤ (20099981241413/20000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (51059772304014508409/50000000000000000000 : ℝ)^1024 ≤ (20099981241413/20000000000000 : ℝ)^4307 := by
      have hnat : (51059772304014508409 : ℕ)^1024*20000000000000^4307 ≤ 20099981241413^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51059772304014508409 50000000000000000000 20099981241413 20000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20099981241413/20000000000000 : ℝ)) (X := (51059772304014508409/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26059772304014508409/25000000000000000000 : ℝ) ≤ (10099981241413/10000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (26059772304014508409/25000000000000000000 : ℝ)^1024 ≤ (10099981241413/10000000000000 : ℝ)^4307 := by
      have hnat : (26059772304014508409 : ℕ)^1024*10000000000000^4307 ≤ 10099981241413^4307*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26059772304014508409 25000000000000000000 10099981241413 10000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10099981241413/10000000000000 : ℝ)) (X := (26059772304014508409/25000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(99981241413/8000000000000 : ℝ)*(0 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(99981241413/8000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1059772304014508409/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(99981241413/8000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (1 : ℝ)+(99981241413/8000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(20099981241413/20000000000000 : ℝ) by norm_num, show 1+(1059772304014508409/50000000000000000000 : ℝ)+(0 : ℝ)=(51059772304014508409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1059772304014508409/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(99981241413/8000000000000 : ℝ)*(2/5 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(99981241413/8000000000000 : ℝ)*(2/5 : ℝ)=(10099981241413/10000000000000 : ℝ) by norm_num, show 1+2*(1059772304014508409/50000000000000000000 : ℝ)=(26059772304014508409/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(99981241413/8000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (99981241413/8000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(99981241413/8000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (99981241413/8000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(99981241413/8000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (99981241413/8000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-902802273/5000000000 : ℝ)*X 0 0+(5994329297/10000000000 : ℝ)*X 0 1+(2406169317/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1100228153/2000000000 : ℝ)*X 1 0+(-1238575091/5000000000 : ℝ)*X 1 1+(481233907/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2750570269/5000000000 : ℝ)*X 2 0+(1203084691/2500000000 : ℝ)*X 2 1+(-49543017/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2088924961/5000000000 : ℝ)*X 0 0+(3106273323/10000000000 : ℝ)*X 0 1+(223505103/400000000 : ℝ)*X 0 2+(2088924961/5000000000 : ℝ)*X 1 0+(3106273323/10000000000 : ℝ)*X 1 1+(223505103/400000000 : ℝ)*X 1 2+(2088924961/5000000000 : ℝ)*X 2 0+(3106273323/10000000000 : ℝ)*X 2 1+(223505103/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-905014887/5000000000 : ℝ)*X 0 0+(2421374689/5000000000 : ℝ)*X 0 1+(745354071/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2589485947/5000000000 : ℝ)*X 1 0+(-1326657787/10000000000 : ℝ)*X 1 1+(298141613/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5178971853/10000000000 : ℝ)*X 2 0+(2981416299/5000000000 : ℝ)*X 2 1+(-1326657309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4187137441/10000000000 : ℝ)*X 0 0+(2761893641/5000000000 : ℝ)*X 0 1+(3172393963/10000000000 : ℝ)*X 0 2+(4187137441/10000000000 : ℝ)*X 1 0+(2761893641/5000000000 : ℝ)*X 1 1+(3172393963/10000000000 : ℝ)*X 1 2+(4187137441/10000000000 : ℝ)*X 2 0+(2761893641/5000000000 : ℝ)*X 2 1+(3172393963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (593430638136560203731/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124849307/100000000000000 : ℝ)*(base1) + (1398725669/100000000000000 : ℝ)*(base19) + (1363814617/100000000000000 : ℝ)*(base23) + (236996397/100000000000000 : ℝ)*(upper3) + (5505847/10000000000000 : ℝ)*(upper5) + (312262356472357/50000000000000 : ℝ)*(major0) + (312262356472357/50000000000000 : ℝ)*(major1) + (312262356472357/50000000000000 : ℝ)*(major2) + (846035372250573/100000000000000 : ℝ)*(sp0) + (423018947037087/50000000000000 : ℝ)*(sp1) + (423018964492613/50000000000000 : ℝ)*(sp2) + (403007477501599/100000000000000 : ℝ)*(sp3) + (4045398577/100000000000000 : ℝ)*(sp4) + (1166464231/50000000000000 : ℝ)*(sp7) + (50376241909921/12500000000000 : ℝ)*(f.failure) + (846039292799843/100000000000000 : ℝ)*(f.sum) + (263351207641/200000000000000000000000000 : ℝ)*base65 + (1803183701241/400000000000000000000000000 : ℝ)*base67 + (951613980841/400000000000000000000000000 : ℝ)*base69 + (1757528468441/400000000000000000000000000 : ℝ)*base71 + (782405301841/200000000000000000000000000 : ℝ)*base73 + (1125539916041/400000000000000000000000000 : ℝ)*base75 + (1186893077241/400000000000000000000000000 : ℝ)*base77 + (2133052350441/400000000000000000000000000 : ℝ)*base79 + (305213074241/200000000000000000000000000 : ℝ)*base81 + (3432189/1250000000000000000000 : ℝ)*base90 + (3432189/1250000000000000000000 : ℝ)*base92 + (3432189/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (290607121664898249969/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (550442201/50000000000000 : ℝ)*(base19) + (307986419/25000000000000 : ℝ)*(base23) + (129142067/100000000000000 : ℝ)*(base39) + (6461781/5000000000000 : ℝ)*(upper3) + (175063101/100000000000000 : ℝ)*(upper5) + (659034998811499/100000000000000 : ℝ)*(major0) + (659034998811499/100000000000000 : ℝ)*(major1) + (82379358708679/12500000000000 : ℝ)*(major2) + (1250385269/50000000000000 : ℝ)*(sp1) + (6738349/250000000000 : ℝ)*(sp2) + (892790023333159/100000000000000 : ℝ)*(sp4) + (892786421678219/100000000000000 : ℝ)*(sp5) + (17855724503799/2000000000000 : ℝ)*(sp6) + (425279651409683/100000000000000 : ℝ)*(sp7) + (425279651409683/100000000000000 : ℝ)*(f.failure) + (446395076237613/50000000000000 : ℝ)*(f.sum) + (1435685885903/800000000000000000000000000 : ℝ)*base65 + (402929652627/100000000000000000000000000 : ℝ)*base67 + (2701173424713/800000000000000000000000000 : ℝ)*base70 + (445537367527/100000000000000000000000000 : ℝ)*base71 + (586479874097/800000000000000000000000000 : ℝ)*base74 + (3446552744887/800000000000000000000000000 : ℝ)*base75 + (4662060725687/800000000000000000000000000 : ℝ)*base77 + (2926962523287/800000000000000000000000000 : ℝ)*base79 + (1162176263513/400000000000000000000000000 : ℝ)*base82 + (95623847/10000000000000000000000 : ℝ)*base90 + (95623847/10000000000000000000000 : ℝ)*base92 + (95623847/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1348_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1459/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6707/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1348_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1348_s1_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-397910921/2000000000 : ℝ)*x 0 + (5639453347/10000000000 : ℝ)*x 1 + (5049405013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397910921/2000000000 : ℝ)^1077 ≤ (375792010539/3125000000000 : ℝ)^821 := by
    have hnat : (397910921 : ℕ)^1077*3125000000000^821 ≤ 375792010539^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397910921 2000000000 375792010539 3125000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5639453347/10000000000 : ℝ)^1077 ≤ (47170340458051/100000000000000 : ℝ)^821 := by
    have hnat : (5639453347 : ℕ)^1077*100000000000000^821 ≤ 47170340458051^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639453347 10000000000 47170340458051 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5049405013/10000000000 : ℝ)^1077 ≤ (40804315186569/100000000000000 : ℝ)^821 := by
    have hnat : (5049405013 : ℕ)^1077*100000000000000^821 ≤ 40804315186569^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049405013 10000000000 40804315186569 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397910921/2000000000 : ℝ), (5639453347/10000000000 : ℝ), (5049405013/10000000000 : ℝ)] ![(375792010539/3125000000000 : ℝ), (47170340458051/100000000000000 : ℝ), (40804315186569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397910921/2000000000 : ℝ)|^1077 ≤ (375792010539/3125000000000 : ℝ)^821
        have hw : |(-397910921/2000000000 : ℝ)|=(397910921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5639453347/10000000000 : ℝ)|^1077 ≤ (47170340458051/100000000000000 : ℝ)^821
        have hw : |(5639453347/10000000000 : ℝ)|=(5639453347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5049405013/10000000000 : ℝ)|^1077 ≤ (40804315186569/100000000000000 : ℝ)^821
        have hw : |(5049405013/10000000000 : ℝ)|=(5049405013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s1_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2702546247/5000000000 : ℝ)*x 0 + (-576064277/2500000000 : ℝ)*x 1 + (2524702667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702546247/5000000000 : ℝ)^1077 ≤ (8923128994737/20000000000000 : ℝ)^821 := by
    have hnat : (2702546247 : ℕ)^1077*20000000000000^821 ≤ 8923128994737^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702546247 5000000000 8923128994737 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576064277/2500000000 : ℝ)^1077 ≤ (7290018211211/50000000000000 : ℝ)^821 := by
    have hnat : (576064277 : ℕ)^1077*50000000000000^821 ≤ 7290018211211^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576064277 2500000000 7290018211211 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2524702667/5000000000 : ℝ)^1077 ≤ (2550269911839/6250000000000 : ℝ)^821 := by
    have hnat : (2524702667 : ℕ)^1077*6250000000000^821 ≤ 2550269911839^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524702667 5000000000 2550269911839 6250000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702546247/5000000000 : ℝ), (-576064277/2500000000 : ℝ), (2524702667/5000000000 : ℝ)] ![(8923128994737/20000000000000 : ℝ), (7290018211211/50000000000000 : ℝ), (2550269911839/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702546247/5000000000 : ℝ)|^1077 ≤ (8923128994737/20000000000000 : ℝ)^821
        have hw : |(2702546247/5000000000 : ℝ)|=(2702546247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-576064277/2500000000 : ℝ)|^1077 ≤ (7290018211211/50000000000000 : ℝ)^821
        have hw : |(-576064277/2500000000 : ℝ)|=(576064277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2524702667/5000000000 : ℝ)|^1077 ≤ (2550269911839/6250000000000 : ℝ)^821
        have hw : |(2524702667/5000000000 : ℝ)|=(2524702667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s1_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5405092461/10000000000 : ℝ)*x 0 + (5049405007/10000000000 : ℝ)*x 1 + (-2304257569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405092461/10000000000 : ℝ)^1077 ≤ (8923128923271/20000000000000 : ℝ)^821 := by
    have hnat : (5405092461 : ℕ)^1077*20000000000000^821 ≤ 8923128923271^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405092461 10000000000 8923128923271 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5049405007/10000000000 : ℝ)^1077 ≤ (10201078780741/25000000000000 : ℝ)^821 := by
    have hnat : (5049405007 : ℕ)^1077*25000000000000^821 ≤ 10201078780741^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049405007 10000000000 10201078780741 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2304257569/10000000000 : ℝ)^1077 ≤ (14580040248917/100000000000000 : ℝ)^821 := by
    have hnat : (2304257569 : ℕ)^1077*100000000000000^821 ≤ 14580040248917^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2304257569 10000000000 14580040248917 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405092461/10000000000 : ℝ), (5049405007/10000000000 : ℝ), (-2304257569/10000000000 : ℝ)] ![(8923128923271/20000000000000 : ℝ), (10201078780741/25000000000000 : ℝ), (14580040248917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405092461/10000000000 : ℝ)|^1077 ≤ (8923128923271/20000000000000 : ℝ)^821
        have hw : |(5405092461/10000000000 : ℝ)|=(5405092461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5049405007/10000000000 : ℝ)|^1077 ≤ (10201078780741/25000000000000 : ℝ)^821
        have hw : |(5049405007/10000000000 : ℝ)|=(5049405007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2304257569/10000000000 : ℝ)|^1077 ≤ (14580040248917/100000000000000 : ℝ)^821
        have hw : |(-2304257569/10000000000 : ℝ)|=(2304257569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s1_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4291237637/10000000000 : ℝ)*x 0 + (3713205649/10000000000 : ℝ)*x 1 + (4951893259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291237637/10000000000 : ℝ)^1077 ≤ (32962212077227/100000000000000 : ℝ)^821 := by
    have hnat : (4291237637 : ℕ)^1077*100000000000000^821 ≤ 32962212077227^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291237637 10000000000 32962212077227 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3713205649/10000000000 : ℝ)^1077 ≤ (13632024322473/50000000000000 : ℝ)^821 := by
    have hnat : (3713205649 : ℕ)^1077*50000000000000^821 ≤ 13632024322473^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713205649 10000000000 13632024322473 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4951893259/10000000000 : ℝ)^1077 ≤ (39773739263241/100000000000000 : ℝ)^821 := by
    have hnat : (4951893259 : ℕ)^1077*100000000000000^821 ≤ 39773739263241^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4951893259 10000000000 39773739263241 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291237637/10000000000 : ℝ), (3713205649/10000000000 : ℝ), (4951893259/10000000000 : ℝ)] ![(32962212077227/100000000000000 : ℝ), (13632024322473/50000000000000 : ℝ), (39773739263241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291237637/10000000000 : ℝ)|^1077 ≤ (32962212077227/100000000000000 : ℝ)^821
        have hw : |(4291237637/10000000000 : ℝ)|=(4291237637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3713205649/10000000000 : ℝ)|^1077 ≤ (13632024322473/50000000000000 : ℝ)^821
        have hw : |(3713205649/10000000000 : ℝ)|=(3713205649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4951893259/10000000000 : ℝ)|^1077 ≤ (39773739263241/100000000000000 : ℝ)^821
        have hw : |(4951893259/10000000000 : ℝ)|=(4951893259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s1_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-995040161/5000000000 : ℝ)*x 0 + (1264193701/2500000000 : ℝ)*x 1 + (5631950113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (995040161/5000000000 : ℝ)^1077 ≤ (751844554913/6250000000000 : ℝ)^821 := by
    have hnat : (995040161 : ℕ)^1077*6250000000000^821 ≤ 751844554913^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995040161 5000000000 751844554913 6250000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1264193701/2500000000 : ℝ)^1077 ≤ (40882458601307/100000000000000 : ℝ)^821 := by
    have hnat : (1264193701 : ℕ)^1077*100000000000000^821 ≤ 40882458601307^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264193701 2500000000 40882458601307 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5631950113/10000000000 : ℝ)^1077 ≤ (11772007125819/25000000000000 : ℝ)^821 := by
    have hnat : (5631950113 : ℕ)^1077*25000000000000^821 ≤ 11772007125819^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5631950113 10000000000 11772007125819 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-995040161/5000000000 : ℝ), (1264193701/2500000000 : ℝ), (5631950113/10000000000 : ℝ)] ![(751844554913/6250000000000 : ℝ), (40882458601307/100000000000000 : ℝ), (11772007125819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-995040161/5000000000 : ℝ)|^1077 ≤ (751844554913/6250000000000 : ℝ)^821
        have hw : |(-995040161/5000000000 : ℝ)|=(995040161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1264193701/2500000000 : ℝ)|^1077 ≤ (40882458601307/100000000000000 : ℝ)^821
        have hw : |(1264193701/2500000000 : ℝ)|=(1264193701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5631950113/10000000000 : ℝ)|^1077 ≤ (11772007125819/25000000000000 : ℝ)^821
        have hw : |(5631950113/10000000000 : ℝ)|=(5631950113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s1_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (525190667/1000000000 : ℝ)*x 0 + (-1721712049/10000000000 : ℝ)*x 1 + (5631950159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525190667/1000000000 : ℝ)^1077 ≤ (671317100679/1562500000000 : ℝ)^821 := by
    have hnat : (525190667 : ℕ)^1077*1562500000000^821 ≤ 671317100679^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525190667 1000000000 671317100679 1562500000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1721712049/10000000000 : ℝ)^1077 ≤ (9947676533661/100000000000000 : ℝ)^821 := by
    have hnat : (1721712049 : ℕ)^1077*100000000000000^821 ≤ 9947676533661^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721712049 10000000000 9947676533661 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5631950159/10000000000 : ℝ)^1077 ≤ (235440145039/500000000000 : ℝ)^821 := by
    have hnat : (5631950159 : ℕ)^1077*500000000000^821 ≤ 235440145039^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5631950159 10000000000 235440145039 500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525190667/1000000000 : ℝ), (-1721712049/10000000000 : ℝ), (5631950159/10000000000 : ℝ)] ![(671317100679/1562500000000 : ℝ), (9947676533661/100000000000000 : ℝ), (235440145039/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525190667/1000000000 : ℝ)|^1077 ≤ (671317100679/1562500000000 : ℝ)^821
        have hw : |(525190667/1000000000 : ℝ)|=(525190667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1721712049/10000000000 : ℝ)|^1077 ≤ (9947676533661/100000000000000 : ℝ)^821
        have hw : |(-1721712049/10000000000 : ℝ)|=(1721712049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5631950159/10000000000 : ℝ)|^1077 ≤ (235440145039/500000000000 : ℝ)^821
        have hw : |(5631950159/10000000000 : ℝ)|=(5631950159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s1_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (656488321/1250000000 : ℝ)*x 0 + (1407987557/2500000000 : ℝ)*x 1 + (-430428023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656488321/1250000000 : ℝ)^1077 ≤ (10741073337209/25000000000000 : ℝ)^821 := by
    have hnat : (656488321 : ℕ)^1077*25000000000000^821 ≤ 10741073337209^821*1250000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656488321 1250000000 10741073337209 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1407987557/2500000000 : ℝ)^1077 ≤ (23544014882293/50000000000000 : ℝ)^821 := by
    have hnat : (1407987557 : ℕ)^1077*50000000000000^821 ≤ 23544014882293^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407987557 2500000000 23544014882293 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430428023/2500000000 : ℝ)^1077 ≤ (4973838429787/50000000000000 : ℝ)^821 := by
    have hnat : (430428023 : ℕ)^1077*50000000000000^821 ≤ 4973838429787^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430428023 2500000000 4973838429787 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656488321/1250000000 : ℝ), (1407987557/2500000000 : ℝ), (-430428023/2500000000 : ℝ)] ![(10741073337209/25000000000000 : ℝ), (23544014882293/50000000000000 : ℝ), (4973838429787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656488321/1250000000 : ℝ)|^1077 ≤ (10741073337209/25000000000000 : ℝ)^821
        have hw : |(656488321/1250000000 : ℝ)|=(656488321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1407987557/2500000000 : ℝ)|^1077 ≤ (23544014882293/50000000000000 : ℝ)^821
        have hw : |(1407987557/2500000000 : ℝ)|=(1407987557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430428023/2500000000 : ℝ)|^1077 ≤ (4973838429787/50000000000000 : ℝ)^821
        have hw : |(-430428023/2500000000 : ℝ)|=(430428023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s1_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2146170799/5000000000 : ℝ)*x 0 + (4936422477/10000000000 : ℝ)*x 1 + (932238943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146170799/5000000000 : ℝ)^1077 ≤ (6594667299967/20000000000000 : ℝ)^821 := by
    have hnat : (2146170799 : ℕ)^1077*20000000000000^821 ≤ 6594667299967^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146170799 5000000000 6594667299967 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4936422477/10000000000 : ℝ)^1077 ≤ (39610810328811/100000000000000 : ℝ)^821 := by
    have hnat : (4936422477 : ℕ)^1077*100000000000000^821 ≤ 39610810328811^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936422477 10000000000 39610810328811 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932238943/2500000000 : ℝ)^1077 ≤ (13707926576507/50000000000000 : ℝ)^821 := by
    have hnat : (932238943 : ℕ)^1077*50000000000000^821 ≤ 13707926576507^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932238943 2500000000 13707926576507 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146170799/5000000000 : ℝ), (4936422477/10000000000 : ℝ), (932238943/2500000000 : ℝ)] ![(6594667299967/20000000000000 : ℝ), (39610810328811/100000000000000 : ℝ), (13707926576507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146170799/5000000000 : ℝ)|^1077 ≤ (6594667299967/20000000000000 : ℝ)^821
        have hw : |(2146170799/5000000000 : ℝ)|=(2146170799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4936422477/10000000000 : ℝ)|^1077 ≤ (39610810328811/100000000000000 : ℝ)^821
        have hw : |(4936422477/10000000000 : ℝ)|=(4936422477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(932238943/2500000000 : ℝ)|^1077 ≤ (13707926576507/50000000000000 : ℝ)^821
        have hw : |(932238943/2500000000 : ℝ)|=(932238943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6707/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1459/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1389/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19417/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6707/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1459/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6707/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1459/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6707/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1459/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6707/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1459/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6707/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1459/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6707/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1459/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1459/100000 : ℝ) ^ (4307/1024 : ℝ) ≤ (948169887881/50000000000000000000 : ℝ) := by
    have hpowers : (1459/100000 : ℝ)^4307 ≤ (948169887881/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1459 : ℕ)^4307*50000000000000000000^1024 ≤ 948169887881^1024*100000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1459 100000 948169887881 50000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1459/100000 : ℝ)) (X := (948169887881/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6707/25000 : ℝ) ^ (4307/1024 : ℝ) ≤ (395012765599074239/100000000000000000000 : ℝ) := by
    have hpowers : (6707/25000 : ℝ)^4307 ≤ (395012765599074239/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6707 : ℕ)^4307*100000000000000000000^1024 ≤ 395012765599074239^1024*25000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6707 25000 395012765599074239 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6707/25000 : ℝ)) (X := (395012765599074239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000948169887881/25000000000000000000 : ℝ) ≤ (5000000045085951/5000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (25000000948169887881/25000000000000000000 : ℝ)^1024 ≤ (5000000045085951/5000000000000000 : ℝ)^4307 := by
      have hnat : (25000000948169887881 : ℕ)^1024*5000000000000000^4307 ≤ 5000000045085951^4307*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000948169887881 25000000000000000000 5000000045085951 5000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000045085951/5000000000000000 : ℝ)) (X := (25000000948169887881/25000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100395014661938850001/100000000000000000000 : ℝ) ≤ (1000937746593713/1000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (100395014661938850001/100000000000000000000 : ℝ)^1024 ≤ (1000937746593713/1000000000000000 : ℝ)^4307 := by
      have hnat : (100395014661938850001 : ℕ)^1024*1000000000000000^4307 ≤ 1000937746593713^4307*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100395014661938850001 100000000000000000000 1000937746593713 1000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000937746593713/1000000000000000 : ℝ)) (X := (100395014661938850001/100000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50395012765599074239/50000000000000000000 : ℝ) ≤ (5009377420851179/5000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50395012765599074239/50000000000000000000 : ℝ)^1024 ≤ (5009377420851179/5000000000000000 : ℝ)^4307 := by
      have hnat : (50395012765599074239 : ℕ)^1024*5000000000000000^4307 ≤ 5009377420851179^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50395012765599074239 50000000000000000000 5009377420851179 5000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009377420851179/5000000000000000 : ℝ)) (X := (50395012765599074239/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(948169887881/50000000000000000000 : ℝ) ≤ ((126831319552544023267/126845000000000000000 : ℝ)+2*(2344343941307/634225000000000 : ℝ)*(1459/100000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (126831319552544023267/126845000000000000000 : ℝ)+2*(2344343941307/634225000000000 : ℝ)*(1459/100000 : ℝ)=(5000000045085951/5000000000000000 : ℝ) by norm_num, show 1+2*(948169887881/50000000000000000000 : ℝ)=(25000000948169887881/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(395012765599074239/100000000000000000000 : ℝ)+(948169887881/50000000000000000000 : ℝ) ≤ ((126831319552544023267/126845000000000000000 : ℝ)+(2344343941307/634225000000000 : ℝ)*((6707/25000 : ℝ)+(1459/100000 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (126831319552544023267/126845000000000000000 : ℝ)+(2344343941307/634225000000000 : ℝ)*((6707/25000 : ℝ)+(1459/100000 : ℝ))=(1000937746593713/1000000000000000 : ℝ) by norm_num, show 1+(395012765599074239/100000000000000000000 : ℝ)+(948169887881/50000000000000000000 : ℝ)=(100395014661938850001/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(395012765599074239/100000000000000000000 : ℝ) ≤ ((126831319552544023267/126845000000000000000 : ℝ)+2*(2344343941307/634225000000000 : ℝ)*(6707/25000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (126831319552544023267/126845000000000000000 : ℝ)+2*(2344343941307/634225000000000 : ℝ)*(6707/25000 : ℝ)=(5009377420851179/5000000000000000 : ℝ) by norm_num, show 1+2*(395012765599074239/100000000000000000000 : ℝ)=(50395012765599074239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (126831319552544023267/126845000000000000000 : ℝ)*(X 1 0+X 2 0)+(2344343941307/634225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (1459/100000 : ℝ)) (hi := (6707/25000 : ℝ)) (c := (126831319552544023267/126845000000000000000 : ℝ)) (alpha := (2344343941307/634225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (126831319552544023267/126845000000000000000 : ℝ)*(X 0 1+X 2 1)+(2344343941307/634225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (1459/100000 : ℝ)) (hi := (6707/25000 : ℝ)) (c := (126831319552544023267/126845000000000000000 : ℝ)) (alpha := (2344343941307/634225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (126831319552544023267/126845000000000000000 : ℝ)*(X 0 2+X 1 2)+(2344343941307/634225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (1459/100000 : ℝ)) (hi := (6707/25000 : ℝ)) (c := (126831319552544023267/126845000000000000000 : ℝ)) (alpha := (2344343941307/634225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-397910921/2000000000 : ℝ)*X 0 0+(5639453347/10000000000 : ℝ)*X 0 1+(5049405013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2702546247/5000000000 : ℝ)*X 1 0+(-576064277/2500000000 : ℝ)*X 1 1+(2524702667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5405092461/10000000000 : ℝ)*X 2 0+(5049405007/10000000000 : ℝ)*X 2 1+(-2304257569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4291237637/10000000000 : ℝ)*X 0 0+(3713205649/10000000000 : ℝ)*X 0 1+(4951893259/10000000000 : ℝ)*X 0 2+(4291237637/10000000000 : ℝ)*X 1 0+(3713205649/10000000000 : ℝ)*X 1 1+(4951893259/10000000000 : ℝ)*X 1 2+(4291237637/10000000000 : ℝ)*X 2 0+(3713205649/10000000000 : ℝ)*X 2 1+(4951893259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-995040161/5000000000 : ℝ)*X 0 0+(1264193701/2500000000 : ℝ)*X 0 1+(5631950113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525190667/1000000000 : ℝ)*X 1 0+(-1721712049/10000000000 : ℝ)*X 1 1+(5631950159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((656488321/1250000000 : ℝ)*X 2 0+(1407987557/2500000000 : ℝ)*X 2 1+(-430428023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2146170799/5000000000 : ℝ)*X 0 0+(4936422477/10000000000 : ℝ)*X 0 1+(932238943/2500000000 : ℝ)*X 0 2+(2146170799/5000000000 : ℝ)*X 1 0+(4936422477/10000000000 : ℝ)*X 1 1+(932238943/2500000000 : ℝ)*X 1 2+(2146170799/5000000000 : ℝ)*X 2 0+(4936422477/10000000000 : ℝ)*X 2 1+(932238943/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12223263670814885547310101/1268450000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31798437/50000000000000 : ℝ)*(base1) + (806519757/50000000000000 : ℝ)*(base19) + (1602692189/100000000000000 : ℝ)*(base23) + (138063191/50000000000000 : ℝ)*(upper3) + (10419027/12500000000000 : ℝ)*(upper5) + (250211215499/20000000000 : ℝ)*(major0) + (250211215499/20000000000 : ℝ)*(major1) + (250211215499/20000000000 : ℝ)*(major2) + (1694787770641633/100000000000000 : ℝ)*(sp0) + (423698861150567/25000000000000 : ℝ)*(sp1) + (211849431868699/12500000000000 : ℝ)*(sp2) + (12614216662581/1562500000000 : ℝ)*(sp3) + (9350597023/100000000000000 : ℝ)*(sp4) + (1211533389/25000000000000 : ℝ)*(sp7) + (403657388067807/50000000000000 : ℝ)*(f.failure) + (847398528820891/50000000000000 : ℝ)*(f.sum) + (814889000877/1014760000000000000000000000 : ℝ)*base66 + (11215189109734667/2536900000000000000000000000000 : ℝ)*base68 + (2159517802094833/2536900000000000000000000000000 : ℝ)*base69 + (5658673655731967/2536900000000000000000000000000 : ℝ)*base72 + (8079497212349/6342250000000000000000000000 : ℝ)*base74 + (8885657385555233/2536900000000000000000000000000 : ℝ)*base75 + (11409463916980033/2536900000000000000000000000000 : ℝ)*base77 + (16806893297028433/2536900000000000000000000000000 : ℝ)*base79 + (934652880619/634225000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (25925437/5000000000000000000000 : ℝ)*base89 + (25925437/5000000000000000000000 : ℝ)*base91 + (25925437/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31667019248416480100263431087/3171125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27183969/25000000000000 : ℝ)*(base1) + (2036918251/100000000000000 : ℝ)*(base19) + (400047147/20000000000000 : ℝ)*(base23) + (230097089/100000000000000 : ℝ)*(upper3) + (4433307/2000000000000 : ℝ)*(upper5) + (1283390352911513/100000000000000 : ℝ)*(major0) + (1283390352911513/100000000000000 : ℝ)*(major1) + (1283390352911513/100000000000000 : ℝ)*(major2) + (1301181013/12500000000000 : ℝ)*(sp1) + (10309459323/100000000000000 : ℝ)*(sp2) + (434650045846519/25000000000000 : ℝ)*(sp4) + (434646907070961/25000000000000 : ℝ)*(sp5) + (869293882477571/50000000000000 : ℝ)*(sp6) + (828180189568541/100000000000000 : ℝ)*(sp7) + (414090149152209/50000000000000 : ℝ)*(f.failure) + (8693000373251/500000000000 : ℝ)*(f.sum) + (31048328797547/63422500000000000000000000000 : ℝ)*base65 + (102438953289057872971/12684500000000000000000000000000000 : ℝ)*base67 + (92977964271982372971/12684500000000000000000000000000000 : ℝ)*base69 + (52973028354259372971/12684500000000000000000000000000000 : ℝ)*base71 + (228183612140341/126845000000000000000000000000 : ℝ)*base74 + (131083580519014372971/12684500000000000000000000000000000 : ℝ)*base75 + (57300146344555872971/12684500000000000000000000000000000 : ℝ)*base77 + (10382996240280627029/12684500000000000000000000000000000 : ℝ)*base80 + (316174635457881/126845000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9463981/5000000000000000000000 : ℝ)*base90 + (9463981/5000000000000000000000 : ℝ)*base92 + (9463981/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1348_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6707/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1459/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1389/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19417/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1348_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1348_s2_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-63412123/312500000 : ℝ)*x 0 + (2739062751/5000000000 : ℝ)*x 1 + (2592668441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63412123/312500000 : ℝ)^1077 ≤ (12340565538767/100000000000000 : ℝ)^821 := by
    have hnat : (63412123 : ℕ)^1077*100000000000000^821 ≤ 12340565538767^821*312500000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63412123 312500000 12340565538767 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739062751/5000000000 : ℝ)^1077 ≤ (45408122381779/100000000000000 : ℝ)^821 := by
    have hnat : (2739062751 : ℕ)^1077*100000000000000^821 ≤ 45408122381779^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739062751 5000000000 45408122381779 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592668441/5000000000 : ℝ)^1077 ≤ (10562828016183/25000000000000 : ℝ)^821 := by
    have hnat : (2592668441 : ℕ)^1077*25000000000000^821 ≤ 10562828016183^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592668441 5000000000 10562828016183 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63412123/312500000 : ℝ), (2739062751/5000000000 : ℝ), (2592668441/5000000000 : ℝ)] ![(12340565538767/100000000000000 : ℝ), (45408122381779/100000000000000 : ℝ), (10562828016183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63412123/312500000 : ℝ)|^1077 ≤ (12340565538767/100000000000000 : ℝ)^821
        have hw : |(-63412123/312500000 : ℝ)|=(63412123/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739062751/5000000000 : ℝ)|^1077 ≤ (45408122381779/100000000000000 : ℝ)^821
        have hw : |(2739062751/5000000000 : ℝ)|=(2739062751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592668441/5000000000 : ℝ)|^1077 ≤ (10562828016183/25000000000000 : ℝ)^821
        have hw : |(2592668441/5000000000 : ℝ)|=(2592668441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s2_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2682767109/5000000000 : ℝ)*x 0 + (-109021227/500000000 : ℝ)*x 1 + (5185337273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682767109/5000000000 : ℝ)^1077 ≤ (22093894656681/50000000000000 : ℝ)^821 := by
    have hnat : (2682767109 : ℕ)^1077*50000000000000^821 ≤ 22093894656681^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682767109 5000000000 22093894656681 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109021227/500000000 : ℝ)^1077 ≤ (2712178885037/20000000000000 : ℝ)^821 := by
    have hnat : (109021227 : ℕ)^1077*20000000000000^821 ≤ 2712178885037^821*500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109021227 500000000 2712178885037 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185337273/10000000000 : ℝ)^1077 ≤ (21125658122059/50000000000000 : ℝ)^821 := by
    have hnat : (5185337273 : ℕ)^1077*50000000000000^821 ≤ 21125658122059^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185337273 10000000000 21125658122059 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682767109/5000000000 : ℝ), (-109021227/500000000 : ℝ), (5185337273/10000000000 : ℝ)] ![(22093894656681/50000000000000 : ℝ), (2712178885037/20000000000000 : ℝ), (21125658122059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682767109/5000000000 : ℝ)|^1077 ≤ (22093894656681/50000000000000 : ℝ)^821
        have hw : |(2682767109/5000000000 : ℝ)|=(2682767109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109021227/500000000 : ℝ)|^1077 ≤ (2712178885037/20000000000000 : ℝ)^821
        have hw : |(-109021227/500000000 : ℝ)|=(109021227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185337273/10000000000 : ℝ)|^1077 ≤ (21125658122059/50000000000000 : ℝ)^821
        have hw : |(5185337273/10000000000 : ℝ)|=(5185337273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s2_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (670691787/1250000000 : ℝ)*x 0 + (162041787/312500000 : ℝ)*x 1 + (-1090212277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670691787/1250000000 : ℝ)^1077 ≤ (4418779015603/10000000000000 : ℝ)^821 := by
    have hnat : (670691787 : ℕ)^1077*10000000000000^821 ≤ 4418779015603^821*1250000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670691787 1250000000 4418779015603 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162041787/312500000 : ℝ)^1077 ≤ (13203536029/31250000000 : ℝ)^821 := by
    have hnat : (162041787 : ℕ)^1077*31250000000^821 ≤ 13203536029^821*312500000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162041787 312500000 13203536029 31250000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090212277/5000000000 : ℝ)^1077 ≤ (13560894539407/100000000000000 : ℝ)^821 := by
    have hnat : (1090212277 : ℕ)^1077*100000000000000^821 ≤ 13560894539407^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090212277 5000000000 13560894539407 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670691787/1250000000 : ℝ), (162041787/312500000 : ℝ), (-1090212277/5000000000 : ℝ)] ![(4418779015603/10000000000000 : ℝ), (13203536029/31250000000 : ℝ), (13560894539407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670691787/1250000000 : ℝ)|^1077 ≤ (4418779015603/10000000000000 : ℝ)^821
        have hw : |(670691787/1250000000 : ℝ)|=(670691787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162041787/312500000 : ℝ)|^1077 ≤ (13203536029/31250000000 : ℝ)^821
        have hw : |(162041787/312500000 : ℝ)|=(162041787/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1090212277/5000000000 : ℝ)|^1077 ≤ (13560894539407/100000000000000 : ℝ)^821
        have hw : |(-1090212277/5000000000 : ℝ)|=(1090212277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s2_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1079742959/2500000000 : ℝ)*x 0 + (804362519/2000000000 : ℝ)*x 1 + (2318231751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079742959/2500000000 : ℝ)^1077 ≤ (6648390947149/20000000000000 : ℝ)^821 := by
    have hnat : (1079742959 : ℕ)^1077*20000000000000^821 ≤ 6648390947149^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079742959 2500000000 6648390947149 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804362519/2000000000 : ℝ)^1077 ≤ (30274339589477/100000000000000 : ℝ)^821 := by
    have hnat : (804362519 : ℕ)^1077*100000000000000^821 ≤ 30274339589477^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804362519 2000000000 30274339589477 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2318231751/5000000000 : ℝ)^1077 ≤ (18241852831491/50000000000000 : ℝ)^821 := by
    have hnat : (2318231751 : ℕ)^1077*50000000000000^821 ≤ 18241852831491^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318231751 5000000000 18241852831491 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079742959/2500000000 : ℝ), (804362519/2000000000 : ℝ), (2318231751/5000000000 : ℝ)] ![(6648390947149/20000000000000 : ℝ), (30274339589477/100000000000000 : ℝ), (18241852831491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079742959/2500000000 : ℝ)|^1077 ≤ (6648390947149/20000000000000 : ℝ)^821
        have hw : |(1079742959/2500000000 : ℝ)|=(1079742959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804362519/2000000000 : ℝ)|^1077 ≤ (30274339589477/100000000000000 : ℝ)^821
        have hw : |(804362519/2000000000 : ℝ)|=(804362519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2318231751/5000000000 : ℝ)|^1077 ≤ (18241852831491/50000000000000 : ℝ)^821
        have hw : |(2318231751/5000000000 : ℝ)|=(2318231751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s2_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-81170087/400000000 : ℝ)*x 0 + (5187161583/10000000000 : ℝ)*x 1 + (5476284461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81170087/400000000 : ℝ)^1077 ≤ (6170539014889/50000000000000 : ℝ)^821 := by
    have hnat : (81170087 : ℕ)^1077*50000000000000^821 ≤ 6170539014889^821*400000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81170087 400000000 6170539014889 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187161583/10000000000 : ℝ)^1077 ≤ (66048152039/156250000000 : ℝ)^821 := by
    have hnat : (5187161583 : ℕ)^1077*156250000000^821 ≤ 66048152039^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187161583 10000000000 66048152039 156250000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476284461/10000000000 : ℝ)^1077 ≤ (45388104652313/100000000000000 : ℝ)^821 := by
    have hnat : (5476284461 : ℕ)^1077*100000000000000^821 ≤ 45388104652313^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476284461 10000000000 45388104652313 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81170087/400000000 : ℝ), (5187161583/10000000000 : ℝ), (5476284461/10000000000 : ℝ)] ![(6170539014889/50000000000000 : ℝ), (66048152039/156250000000 : ℝ), (45388104652313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81170087/400000000 : ℝ)|^1077 ≤ (6170539014889/50000000000000 : ℝ)^821
        have hw : |(-81170087/400000000 : ℝ)|=(81170087/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187161583/10000000000 : ℝ)|^1077 ≤ (66048152039/156250000000 : ℝ)^821
        have hw : |(5187161583/10000000000 : ℝ)|=(5187161583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476284461/10000000000 : ℝ)|^1077 ≤ (45388104652313/100000000000000 : ℝ)^821
        have hw : |(5476284461/10000000000 : ℝ)|=(5476284461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s2_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2645009523/5000000000 : ℝ)*x 0 + (-1889477053/10000000000 : ℝ)*x 1 + (1095256889/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645009523/5000000000 : ℝ)^1077 ≤ (43373762024733/100000000000000 : ℝ)^821 := by
    have hnat : (2645009523 : ℕ)^1077*100000000000000^821 ≤ 43373762024733^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645009523 5000000000 43373762024733 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889477053/10000000000 : ℝ)^1077 ≤ (1123813348163/10000000000000 : ℝ)^821 := by
    have hnat : (1889477053 : ℕ)^1077*10000000000000^821 ≤ 1123813348163^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889477053 10000000000 1123813348163 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095256889/2000000000 : ℝ)^1077 ≤ (22694052239177/50000000000000 : ℝ)^821 := by
    have hnat : (1095256889 : ℕ)^1077*50000000000000^821 ≤ 22694052239177^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095256889 2000000000 22694052239177 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645009523/5000000000 : ℝ), (-1889477053/10000000000 : ℝ), (1095256889/2000000000 : ℝ)] ![(43373762024733/100000000000000 : ℝ), (1123813348163/10000000000000 : ℝ), (22694052239177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645009523/5000000000 : ℝ)|^1077 ≤ (43373762024733/100000000000000 : ℝ)^821
        have hw : |(2645009523/5000000000 : ℝ)|=(2645009523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1889477053/10000000000 : ℝ)|^1077 ≤ (1123813348163/10000000000000 : ℝ)^821
        have hw : |(-1889477053/10000000000 : ℝ)|=(1889477053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095256889/2000000000 : ℝ)|^1077 ≤ (22694052239177/50000000000000 : ℝ)^821
        have hw : |(1095256889/2000000000 : ℝ)|=(1095256889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s2_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322504761/2500000000 : ℝ)*x 0 + (1369071117/2500000000 : ℝ)*x 1 + (-59046157/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322504761/2500000000 : ℝ)^1077 ≤ (21686881001611/50000000000000 : ℝ)^821 := by
    have hnat : (1322504761 : ℕ)^1077*50000000000000^821 ≤ 21686881001611^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322504761 2500000000 21686881001611 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369071117/2500000000 : ℝ)^1077 ≤ (45388104728421/100000000000000 : ℝ)^821 := by
    have hnat : (1369071117 : ℕ)^1077*100000000000000^821 ≤ 45388104728421^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369071117 2500000000 45388104728421 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59046157/312500000 : ℝ)^1077 ≤ (5619066627681/50000000000000 : ℝ)^821 := by
    have hnat : (59046157 : ℕ)^1077*50000000000000^821 ≤ 5619066627681^821*312500000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59046157 312500000 5619066627681 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322504761/2500000000 : ℝ), (1369071117/2500000000 : ℝ), (-59046157/312500000 : ℝ)] ![(21686881001611/50000000000000 : ℝ), (45388104728421/100000000000000 : ℝ), (5619066627681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322504761/2500000000 : ℝ)|^1077 ≤ (21686881001611/50000000000000 : ℝ)^821
        have hw : |(1322504761/2500000000 : ℝ)|=(1322504761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369071117/2500000000 : ℝ)|^1077 ≤ (45388104728421/100000000000000 : ℝ)^821
        have hw : |(1369071117/2500000000 : ℝ)|=(1369071117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59046157/312500000 : ℝ)|^1077 ≤ (5619066627681/50000000000000 : ℝ)^821
        have hw : |(-59046157/312500000 : ℝ)|=(59046157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s2_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2159553517/5000000000 : ℝ)*x 0 + (4632633539/10000000000 : ℝ)*x 1 + (1006419223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159553517/5000000000 : ℝ)^1077 ≤ (2077707487111/6250000000000 : ℝ)^821 := by
    have hnat : (2159553517 : ℕ)^1077*6250000000000^821 ≤ 2077707487111^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159553517 5000000000 2077707487111 6250000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4632633539/10000000000 : ℝ)^1077 ≤ (9111043996249/25000000000000 : ℝ)^821 := by
    have hnat : (4632633539 : ℕ)^1077*25000000000000^821 ≤ 9111043996249^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4632633539 10000000000 9111043996249 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006419223/2500000000 : ℝ)^1077 ≤ (3789063026057/12500000000000 : ℝ)^821 := by
    have hnat : (1006419223 : ℕ)^1077*12500000000000^821 ≤ 3789063026057^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006419223 2500000000 3789063026057 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159553517/5000000000 : ℝ), (4632633539/10000000000 : ℝ), (1006419223/2500000000 : ℝ)] ![(2077707487111/6250000000000 : ℝ), (9111043996249/25000000000000 : ℝ), (3789063026057/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159553517/5000000000 : ℝ)|^1077 ≤ (2077707487111/6250000000000 : ℝ)^821
        have hw : |(2159553517/5000000000 : ℝ)|=(2159553517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4632633539/10000000000 : ℝ)|^1077 ≤ (9111043996249/25000000000000 : ℝ)^821
        have hw : |(4632633539/10000000000 : ℝ)|=(4632633539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006419223/2500000000 : ℝ)|^1077 ≤ (3789063026057/12500000000000 : ℝ)^821
        have hw : |(1006419223/2500000000 : ℝ)|=(1006419223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19417/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9891/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19417/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1389/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19417/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1389/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19417/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1389/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19417/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1389/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19417/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1389/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19417/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1389/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1389/20000 : ℝ) ^ (4307/1024 : ℝ) ≤ (33569907643571/2500000000000000000 : ℝ) := by
    have hpowers : (1389/20000 : ℝ)^4307 ≤ (33569907643571/2500000000000000000 : ℝ)^1024 := by
      have hnat : (1389 : ℕ)^4307*2500000000000000000^1024 ≤ 33569907643571^1024*20000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1389 20000 33569907643571 2500000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1389/20000 : ℝ)) (X := (33569907643571/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19417/100000 : ℝ) ^ (4307/1024 : ℝ) ≤ (50702003178945999/50000000000000000000 : ℝ) := by
    have hpowers : (19417/100000 : ℝ)^4307 ≤ (50702003178945999/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19417 : ℕ)^4307*50000000000000000000^1024 ≤ 50702003178945999^1024*100000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19417 100000 50702003178945999 50000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19417/100000 : ℝ)) (X := (50702003178945999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250033569907643571/1250000000000000000 : ℝ) ≤ (10000063849981117/10000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (1250033569907643571/1250000000000000000 : ℝ)^1024 ≤ (10000063849981117/10000000000000000 : ℝ)^4307 := by
      have hnat : (1250033569907643571 : ℕ)^1024*10000000000000000^4307 ≤ 10000063849981117^4307*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250033569907643571 1250000000000000000 10000063849981117 10000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063849981117/10000000000000000 : ℝ)) (X := (1250033569907643571/1250000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50051373401331817419/50000000000000000000 : ℝ) ≤ (200048837497221/200000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50051373401331817419/50000000000000000000 : ℝ)^1024 ≤ (200048837497221/200000000000000 : ℝ)^4307 := by
      have hnat : (50051373401331817419 : ℕ)^1024*200000000000000^4307 ≤ 200048837497221^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50051373401331817419 50000000000000000000 200048837497221 200000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200048837497221/200000000000000 : ℝ)) (X := (50051373401331817419/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25050702003178945999/25000000000000000000 : ℝ) ≤ (10004819899740983/10000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (25050702003178945999/25000000000000000000 : ℝ)^1024 ≤ (10004819899740983/10000000000000000 : ℝ)^4307 := by
      have hnat : (25050702003178945999 : ℕ)^1024*10000000000000000^4307 ≤ 10004819899740983^4307*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25050702003178945999 25000000000000000000 10004819899740983 10000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004819899740983/10000000000000000 : ℝ)) (X := (25050702003178945999/25000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(33569907643571/2500000000000000000 : ℝ) ≤ ((62343882785691110927/62360000000000000000 : ℝ)+2*(2378024879933/1247200000000000 : ℝ)*(1389/20000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (62343882785691110927/62360000000000000000 : ℝ)+2*(2378024879933/1247200000000000 : ℝ)*(1389/20000 : ℝ)=(10000063849981117/10000000000000000 : ℝ) by norm_num, show 1+2*(33569907643571/2500000000000000000 : ℝ)=(1250033569907643571/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(50702003178945999/50000000000000000000 : ℝ)+(33569907643571/2500000000000000000 : ℝ) ≤ ((62343882785691110927/62360000000000000000 : ℝ)+(2378024879933/1247200000000000 : ℝ)*((19417/100000 : ℝ)+(1389/20000 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (62343882785691110927/62360000000000000000 : ℝ)+(2378024879933/1247200000000000 : ℝ)*((19417/100000 : ℝ)+(1389/20000 : ℝ))=(200048837497221/200000000000000 : ℝ) by norm_num, show 1+(50702003178945999/50000000000000000000 : ℝ)+(33569907643571/2500000000000000000 : ℝ)=(50051373401331817419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(50702003178945999/50000000000000000000 : ℝ) ≤ ((62343882785691110927/62360000000000000000 : ℝ)+2*(2378024879933/1247200000000000 : ℝ)*(19417/100000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (62343882785691110927/62360000000000000000 : ℝ)+2*(2378024879933/1247200000000000 : ℝ)*(19417/100000 : ℝ)=(10004819899740983/10000000000000000 : ℝ) by norm_num, show 1+2*(50702003178945999/50000000000000000000 : ℝ)=(25050702003178945999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (62343882785691110927/62360000000000000000 : ℝ)*(X 1 0+X 2 0)+(2378024879933/1247200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (1389/20000 : ℝ)) (hi := (19417/100000 : ℝ)) (c := (62343882785691110927/62360000000000000000 : ℝ)) (alpha := (2378024879933/1247200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (62343882785691110927/62360000000000000000 : ℝ)*(X 0 1+X 2 1)+(2378024879933/1247200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (1389/20000 : ℝ)) (hi := (19417/100000 : ℝ)) (c := (62343882785691110927/62360000000000000000 : ℝ)) (alpha := (2378024879933/1247200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (62343882785691110927/62360000000000000000 : ℝ)*(X 0 2+X 1 2)+(2378024879933/1247200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (1389/20000 : ℝ)) (hi := (19417/100000 : ℝ)) (c := (62343882785691110927/62360000000000000000 : ℝ)) (alpha := (2378024879933/1247200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-63412123/312500000 : ℝ)*X 0 0+(2739062751/5000000000 : ℝ)*X 0 1+(2592668441/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682767109/5000000000 : ℝ)*X 1 0+(-109021227/500000000 : ℝ)*X 1 1+(5185337273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((670691787/1250000000 : ℝ)*X 2 0+(162041787/312500000 : ℝ)*X 2 1+(-1090212277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079742959/2500000000 : ℝ)*X 0 0+(804362519/2000000000 : ℝ)*X 0 1+(2318231751/5000000000 : ℝ)*X 0 2+(1079742959/2500000000 : ℝ)*X 1 0+(804362519/2000000000 : ℝ)*X 1 1+(2318231751/5000000000 : ℝ)*X 1 2+(1079742959/2500000000 : ℝ)*X 2 0+(804362519/2000000000 : ℝ)*X 2 1+(2318231751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-81170087/400000000 : ℝ)*X 0 0+(5187161583/10000000000 : ℝ)*X 0 1+(5476284461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645009523/5000000000 : ℝ)*X 1 0+(-1889477053/10000000000 : ℝ)*X 1 1+(1095256889/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322504761/2500000000 : ℝ)*X 2 0+(1369071117/2500000000 : ℝ)*X 2 1+(-59046157/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159553517/5000000000 : ℝ)*X 0 0+(4632633539/10000000000 : ℝ)*X 0 1+(1006419223/2500000000 : ℝ)*X 0 2+(2159553517/5000000000 : ℝ)*X 1 0+(4632633539/10000000000 : ℝ)*X 1 1+(1006419223/2500000000 : ℝ)*X 1 2+(2159553517/5000000000 : ℝ)*X 2 0+(4632633539/10000000000 : ℝ)*X 2 1+(1006419223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (297656136412750911276718401/97437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109423399/25000000000000 : ℝ)*(base19) + (466198793/100000000000000 : ℝ)*(base23) + (70510119/100000000000000 : ℝ)*(upper3) + (5672981/50000000000000 : ℝ)*(upper4) + (6791553/12500000000000 : ℝ)*(upper5) + (78787480217521/3125000000000 : ℝ)*(major0) + (78787480217521/3125000000000 : ℝ)*(major1) + (78787480217521/3125000000000 : ℝ)*(major2) + (1707721282955977/50000000000000 : ℝ)*(sp0) + (426931442221813/12500000000000 : ℝ)*(sp1) + (1707725754634653/50000000000000 : ℝ)*(sp2) + (406735760787343/25000000000000 : ℝ)*(sp3) + (4704778073/50000000000000 : ℝ)*(sp4) + (3613475811/100000000000000 : ℝ)*(sp7) + (1626946656625183/100000000000000 : ℝ)*(f.failure) + (34154519754681/1000000000000 : ℝ)*(f.sum) + (9857806962967/1948750000000000000000000000 : ℝ)*base66 + (618799284183523033/194875000000000000000000000000000 : ℝ)*base68 + (408949971284148033/194875000000000000000000000000000 : ℝ)*base70 + (2537102782575648033/194875000000000000000000000000000 : ℝ)*base72 + (6176980199283/7795000000000000000000000000 : ℝ)*base74 + (609748790513101967/194875000000000000000000000000000 : ℝ)*base75 + (880392672732351967/194875000000000000000000000000000 : ℝ)*base77 + (300156107858773033/194875000000000000000000000000000 : ℝ)*base80 + (4434442650517/1948750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (36486653/10000000000000000000000 : ℝ)*base89 + (36486653/10000000000000000000000 : ℝ)*base91 + (36486653/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16378181863358851244279802171/1559000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130416687/6250000000000 : ℝ)*(base19) + (115842587/5000000000000 : ℝ)*(base23) + (251420927/100000000000000 : ℝ)*(upper3) + (47416291/50000000000000 : ℝ)*(lower4) + (92288681/50000000000000 : ℝ)*(upper5) + (1276574804338809/50000000000000 : ℝ)*(major0) + (1276574804338809/50000000000000 : ℝ)*(major1) + (1276574804338809/50000000000000 : ℝ)*(major2) + (23612324063/100000000000000 : ℝ)*(sp1) + (27270809691/100000000000000 : ℝ)*(sp2) + (27021363342707/781250000000 : ℝ)*(sp4) + (43233860110943/1250000000000 : ℝ)*(sp5) + (691740984041013/20000000000000 : ℝ)*(sp6) + (1647564359303101/100000000000000 : ℝ)*(sp7) + (1647564359303101/100000000000000 : ℝ)*(f.failure) + (27021363342707/781250000000 : ℝ)*(f.sum) + (58760777511677/31180000000000000000000000000 : ℝ)*base65 + (595580914726084057/3118000000000000000000000000000000 : ℝ)*base68 + (30948809951635915943/3118000000000000000000000000000000 : ℝ)*base69 + (39649683551755915943/3118000000000000000000000000000000 : ℝ)*base71 + (162518583467023/31180000000000000000000000000 : ℝ)*base74 + (56716235266161915943/3118000000000000000000000000000000 : ℝ)*base75 + (921740000040084057/3118000000000000000000000000000000 : ℝ)*base78 + (42993256524545915943/3118000000000000000000000000000000 : ℝ)*base79 + (11914276327443/31180000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (56952809/10000000000000000000000 : ℝ)*base90 + (56952809/10000000000000000000000 : ℝ)*base92 + (56952809/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1348_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19417/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1348_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1348_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16081/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1348_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1348_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1348_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16081/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1348_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
