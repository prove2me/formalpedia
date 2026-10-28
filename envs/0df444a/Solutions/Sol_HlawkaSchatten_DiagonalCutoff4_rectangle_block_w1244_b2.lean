-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1244_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:48.255699+00:00
-- url     : https://prove2.me/submissions/b569d1b4-c69e-445e-9403-2a218ce2ec39

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
theorem support_rectangle_w1244_s6_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529756599/2500000000 : ℝ)*x 0 + (2695676089/5000000000 : ℝ)*x 1 + (41148901/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529756599/2500000000 : ℝ)^8437 ≤ (12886314927133/100000000000000 : ℝ)^6389 := by
    have hnat : (529756599 : ℕ)^8437*100000000000000^6389 ≤ 12886314927133^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529756599 2500000000 12886314927133 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695676089/5000000000 : ℝ)^8437 ≤ (8845515382207/20000000000000 : ℝ)^6389 := by
    have hnat : (2695676089 : ℕ)^8437*20000000000000^6389 ≤ 8845515382207^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695676089 5000000000 8845515382207 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41148901/78125000 : ℝ)^8437 ≤ (21443054072689/50000000000000 : ℝ)^6389 := by
    have hnat : (41148901 : ℕ)^8437*50000000000000^6389 ≤ 21443054072689^6389*78125000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41148901 78125000 21443054072689 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529756599/2500000000 : ℝ), (2695676089/5000000000 : ℝ), (41148901/78125000 : ℝ)] ![(12886314927133/100000000000000 : ℝ), (8845515382207/20000000000000 : ℝ), (21443054072689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529756599/2500000000 : ℝ)|^8437 ≤ (12886314927133/100000000000000 : ℝ)^6389
        have hw : |(-529756599/2500000000 : ℝ)|=(529756599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695676089/5000000000 : ℝ)|^8437 ≤ (8845515382207/20000000000000 : ℝ)^6389
        have hw : |(2695676089/5000000000 : ℝ)|=(2695676089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41148901/78125000 : ℝ)|^8437 ≤ (21443054072689/50000000000000 : ℝ)^6389
        have hw : |(41148901/78125000 : ℝ)|=(41148901/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s6_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133608669/250000000 : ℝ)*x 0 + (-2182048221/10000000000 : ℝ)*x 1 + (1316764831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133608669/250000000 : ℝ)^8437 ≤ (43719078011723/100000000000000 : ℝ)^6389 := by
    have hnat : (133608669 : ℕ)^8437*100000000000000^6389 ≤ 43719078011723^6389*250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133608669 250000000 43719078011723 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182048221/10000000000 : ℝ)^8437 ≤ (535792554799/4000000000000 : ℝ)^6389 := by
    have hnat : (2182048221 : ℕ)^8437*4000000000000^6389 ≤ 535792554799^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182048221 10000000000 535792554799 4000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316764831/2500000000 : ℝ)^8437 ≤ (1340190878199/3125000000000 : ℝ)^6389 := by
    have hnat : (1316764831 : ℕ)^8437*3125000000000^6389 ≤ 1340190878199^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316764831 2500000000 1340190878199 3125000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133608669/250000000 : ℝ), (-2182048221/10000000000 : ℝ), (1316764831/2500000000 : ℝ)] ![(43719078011723/100000000000000 : ℝ), (535792554799/4000000000000 : ℝ), (1340190878199/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133608669/250000000 : ℝ)|^8437 ≤ (43719078011723/100000000000000 : ℝ)^6389
        have hw : |(133608669/250000000 : ℝ)|=(133608669/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182048221/10000000000 : ℝ)|^8437 ≤ (535792554799/4000000000000 : ℝ)^6389
        have hw : |(-2182048221/10000000000 : ℝ)|=(2182048221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316764831/2500000000 : ℝ)|^8437 ≤ (1340190878199/3125000000000 : ℝ)^6389
        have hw : |(1316764831/2500000000 : ℝ)|=(1316764831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s6_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213773871/400000000 : ℝ)*x 0 + (2633529659/5000000000 : ℝ)*x 1 + (-2182048209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213773871/400000000 : ℝ)^8437 ≤ (43719078173763/100000000000000 : ℝ)^6389 := by
    have hnat : (213773871 : ℕ)^8437*100000000000000^6389 ≤ 43719078173763^6389*400000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213773871 400000000 43719078173763 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633529659/5000000000 : ℝ)^8437 ≤ (21443054018927/50000000000000 : ℝ)^6389 := by
    have hnat : (2633529659 : ℕ)^8437*50000000000000^6389 ≤ 21443054018927^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633529659 5000000000 21443054018927 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182048209/10000000000 : ℝ)^8437 ≤ (6697406886349/50000000000000 : ℝ)^6389 := by
    have hnat : (2182048209 : ℕ)^8437*50000000000000^6389 ≤ 6697406886349^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182048209 10000000000 6697406886349 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213773871/400000000 : ℝ), (2633529659/5000000000 : ℝ), (-2182048209/10000000000 : ℝ)] ![(43719078173763/100000000000000 : ℝ), (21443054018927/50000000000000 : ℝ), (6697406886349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213773871/400000000 : ℝ)|^8437 ≤ (43719078173763/100000000000000 : ℝ)^6389
        have hw : |(213773871/400000000 : ℝ)|=(213773871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633529659/5000000000 : ℝ)|^8437 ≤ (21443054018927/50000000000000 : ℝ)^6389
        have hw : |(2633529659/5000000000 : ℝ)|=(2633529659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182048209/10000000000 : ℝ)|^8437 ≤ (6697406886349/50000000000000 : ℝ)^6389
        have hw : |(-2182048209/10000000000 : ℝ)|=(2182048209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s6_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350489473/10000000000 : ℝ)*x 0 + (132067151/312500000 : ℝ)*x 1 + (4478383029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350489473/10000000000 : ℝ)^8437 ≤ (33317405523083/100000000000000 : ℝ)^6389 := by
    have hnat : (4350489473 : ℕ)^8437*100000000000000^6389 ≤ 33317405523083^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350489473 10000000000 33317405523083 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132067151/312500000 : ℝ)^8437 ≤ (6413144575477/20000000000000 : ℝ)^6389 := by
    have hnat : (132067151 : ℕ)^8437*20000000000000^6389 ≤ 6413144575477^6389*312500000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132067151 312500000 6413144575477 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478383029/10000000000 : ℝ)^8437 ≤ (135222154617/390625000000 : ℝ)^6389 := by
    have hnat : (4478383029 : ℕ)^8437*390625000000^6389 ≤ 135222154617^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478383029 10000000000 135222154617 390625000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350489473/10000000000 : ℝ), (132067151/312500000 : ℝ), (4478383029/10000000000 : ℝ)] ![(33317405523083/100000000000000 : ℝ), (6413144575477/20000000000000 : ℝ), (135222154617/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350489473/10000000000 : ℝ)|^8437 ≤ (33317405523083/100000000000000 : ℝ)^6389
        have hw : |(4350489473/10000000000 : ℝ)|=(4350489473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132067151/312500000 : ℝ)|^8437 ≤ (6413144575477/20000000000000 : ℝ)^6389
        have hw : |(132067151/312500000 : ℝ)|=(132067151/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478383029/10000000000 : ℝ)|^8437 ≤ (135222154617/390625000000 : ℝ)^6389
        have hw : |(4478383029/10000000000 : ℝ)|=(4478383029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s6_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119031009/10000000000 : ℝ)*x 0 + (658421743/1250000000 : ℝ)*x 1 + (5391036479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119031009/10000000000 : ℝ)^8437 ≤ (2577270394453/20000000000000 : ℝ)^6389 := by
    have hnat : (2119031009 : ℕ)^8437*20000000000000^6389 ≤ 2577270394453^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119031009 10000000000 2577270394453 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658421743/1250000000 : ℝ)^8437 ≤ (21444745520313/50000000000000 : ℝ)^6389 := by
    have hnat : (658421743 : ℕ)^8437*50000000000000^6389 ≤ 21444745520313^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658421743 1250000000 21444745520313 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391036479/10000000000 : ℝ)^8437 ≤ (44224156961201/100000000000000 : ℝ)^6389 := by
    have hnat : (5391036479 : ℕ)^8437*100000000000000^6389 ≤ 44224156961201^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391036479 10000000000 44224156961201 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119031009/10000000000 : ℝ), (658421743/1250000000 : ℝ), (5391036479/10000000000 : ℝ)] ![(2577270394453/20000000000000 : ℝ), (21444745520313/50000000000000 : ℝ), (44224156961201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119031009/10000000000 : ℝ)|^8437 ≤ (2577270394453/20000000000000 : ℝ)^6389
        have hw : |(-2119031009/10000000000 : ℝ)|=(2119031009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658421743/1250000000 : ℝ)|^8437 ≤ (21444745520313/50000000000000 : ℝ)^6389
        have hw : |(658421743/1250000000 : ℝ)|=(658421743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391036479/10000000000 : ℝ)|^8437 ≤ (44224156961201/100000000000000 : ℝ)^6389
        have hw : |(5391036479/10000000000 : ℝ)|=(5391036479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s6_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656314293/5000000000 : ℝ)*x 0 + (-514517673/2500000000 : ℝ)*x 1 + (5391036813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656314293/5000000000 : ℝ)^8437 ≤ (21688381541031/50000000000000 : ℝ)^6389 := by
    have hnat : (2656314293 : ℕ)^8437*50000000000000^6389 ≤ 21688381541031^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656314293 5000000000 21688381541031 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514517673/2500000000 : ℝ)^8437 ≤ (387471135131/3125000000000 : ℝ)^6389 := by
    have hnat : (514517673 : ℕ)^8437*3125000000000^6389 ≤ 387471135131^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514517673 2500000000 387471135131 3125000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391036813/10000000000 : ℝ)^8437 ≤ (44224160579371/100000000000000 : ℝ)^6389 := by
    have hnat : (5391036813 : ℕ)^8437*100000000000000^6389 ≤ 44224160579371^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391036813 10000000000 44224160579371 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656314293/5000000000 : ℝ), (-514517673/2500000000 : ℝ), (5391036813/10000000000 : ℝ)] ![(21688381541031/50000000000000 : ℝ), (387471135131/3125000000000 : ℝ), (44224160579371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656314293/5000000000 : ℝ)|^8437 ≤ (21688381541031/50000000000000 : ℝ)^6389
        have hw : |(2656314293/5000000000 : ℝ)|=(2656314293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514517673/2500000000 : ℝ)|^8437 ≤ (387471135131/3125000000000 : ℝ)^6389
        have hw : |(-514517673/2500000000 : ℝ)|=(514517673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391036813/10000000000 : ℝ)|^8437 ≤ (44224160579371/100000000000000 : ℝ)^6389
        have hw : |(5391036813/10000000000 : ℝ)|=(5391036813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s6_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062525743/2000000000 : ℝ)*x 0 + (2695518327/5000000000 : ℝ)*x 1 + (-1029035367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062525743/2000000000 : ℝ)^8437 ≤ (5422095559119/12500000000000 : ℝ)^6389 := by
    have hnat : (1062525743 : ℕ)^8437*12500000000000^6389 ≤ 5422095559119^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062525743 2000000000 5422095559119 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695518327/5000000000 : ℝ)^8437 ≤ (44224158856949/100000000000000 : ℝ)^6389 := by
    have hnat : (2695518327 : ℕ)^8437*100000000000000^6389 ≤ 44224158856949^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695518327 5000000000 44224158856949 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029035367/5000000000 : ℝ)^8437 ≤ (387471145573/3125000000000 : ℝ)^6389 := by
    have hnat : (1029035367 : ℕ)^8437*3125000000000^6389 ≤ 387471145573^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029035367 5000000000 387471145573 3125000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062525743/2000000000 : ℝ), (2695518327/5000000000 : ℝ), (-1029035367/5000000000 : ℝ)] ![(5422095559119/12500000000000 : ℝ), (44224158856949/100000000000000 : ℝ), (387471145573/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062525743/2000000000 : ℝ)|^8437 ≤ (5422095559119/12500000000000 : ℝ)^6389
        have hw : |(1062525743/2000000000 : ℝ)|=(1062525743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695518327/5000000000 : ℝ)|^8437 ≤ (44224158856949/100000000000000 : ℝ)^6389
        have hw : |(2695518327/5000000000 : ℝ)|=(2695518327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029035367/5000000000 : ℝ)|^8437 ≤ (387471145573/3125000000000 : ℝ)^6389
        have hw : |(-1029035367/5000000000 : ℝ)|=(1029035367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s6_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870099763/2000000000 : ℝ)*x 0 + (4477744919/10000000000 : ℝ)*x 1 + (1056697363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870099763/2000000000 : ℝ)^8437 ≤ (33317500000547/100000000000000 : ℝ)^6389 := by
    have hnat : (870099763 : ℕ)^8437*100000000000000^6389 ≤ 33317500000547^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870099763 2000000000 33317500000547 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477744919/10000000000 : ℝ)^8437 ≤ (34610358187577/100000000000000 : ℝ)^6389 := by
    have hnat : (4477744919 : ℕ)^8437*100000000000000^6389 ≤ 34610358187577^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477744919 10000000000 34610358187577 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056697363/2500000000 : ℝ)^8437 ≤ (32072141804617/100000000000000 : ℝ)^6389 := by
    have hnat : (1056697363 : ℕ)^8437*100000000000000^6389 ≤ 32072141804617^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056697363 2500000000 32072141804617 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870099763/2000000000 : ℝ), (4477744919/10000000000 : ℝ), (1056697363/2500000000 : ℝ)] ![(33317500000547/100000000000000 : ℝ), (34610358187577/100000000000000 : ℝ), (32072141804617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870099763/2000000000 : ℝ)|^8437 ≤ (33317500000547/100000000000000 : ℝ)^6389
        have hw : |(870099763/2000000000 : ℝ)|=(870099763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477744919/10000000000 : ℝ)|^8437 ≤ (34610358187577/100000000000000 : ℝ)^6389
        have hw : |(4477744919/10000000000 : ℝ)|=(4477744919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056697363/2500000000 : ℝ)|^8437 ≤ (32072141804617/100000000000000 : ℝ)^6389
        have hw : |(1056697363/2500000000 : ℝ)|=(1056697363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11477/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14131/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (358/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14131/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (358/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14131/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (358/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14131/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (358/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14131/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (358/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14131/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (358/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (358/3125 : ℝ) ^ (2109/512 : ℝ) ≤ (6652649276216189/50000000000000000000 : ℝ) := by
    have hpowers : (358/3125 : ℝ)^2109 ≤ (6652649276216189/50000000000000000000 : ℝ)^512 := by
      have hnat : (358 : ℕ)^2109*50000000000000000000^512 ≤ 6652649276216189^512*3125^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        358 3125 6652649276216189 50000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (358/3125 : ℝ)) (X := (6652649276216189/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14131/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (493472186162861/1562500000000000000 : ℝ) := by
    have hpowers : (14131/100000 : ℝ)^2109 ≤ (493472186162861/1562500000000000000 : ℝ)^512 := by
      have hnat : (14131 : ℕ)^2109*1562500000000000000^512 ≤ 493472186162861^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14131 100000 493472186162861 1562500000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14131/100000 : ℝ)) (X := (493472186162861/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006652649276216189/25000000000000000000 : ℝ) ≤ (200012919159057/200000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (25006652649276216189/25000000000000000000 : ℝ)^512 ≤ (200012919159057/200000000000000 : ℝ)^2109 := by
      have hnat : (25006652649276216189 : ℕ)^512*200000000000000^2109 ≤ 200012919159057^2109*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006652649276216189 25000000000000000000 200012919159057 200000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200012919159057/200000000000000 : ℝ)) (X := (25006652649276216189/25000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022443759233427741/50000000000000000000 : ℝ) ≤ (10001089545025903/10000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50022443759233427741/50000000000000000000 : ℝ)^512 ≤ (10001089545025903/10000000000000000 : ℝ)^2109 := by
      have hnat : (50022443759233427741 : ℕ)^512*10000000000000000^2109 ≤ 10001089545025903^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022443759233427741 50000000000000000000 10001089545025903 10000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001089545025903/10000000000000000 : ℝ)) (X := (50022443759233427741/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (781743472186162861/781250000000000000 : ℝ) ≤ (2500383283024739/2500000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (781743472186162861/781250000000000000 : ℝ)^512 ≤ (2500383283024739/2500000000000000 : ℝ)^2109 := by
      have hnat : (781743472186162861 : ℕ)^512*2500000000000000^2109 ≤ 2500383283024739^2109*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781743472186162861 781250000000000000 2500383283024739 2500000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500383283024739/2500000000000000 : ℝ)) (X := (781743472186162861/781250000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6652649276216189/50000000000000000000 : ℝ) ≤ ((13370782235253041707/13375000000000000000 : ℝ)+2*(443587073053/267500000000000 : ℝ)*(358/3125 : ℝ))^(2109/512 : ℝ) := by
    rw [show (13370782235253041707/13375000000000000000 : ℝ)+2*(443587073053/267500000000000 : ℝ)*(358/3125 : ℝ)=(200012919159057/200000000000000 : ℝ) by norm_num, show 1+2*(6652649276216189/50000000000000000000 : ℝ)=(25006652649276216189/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(493472186162861/1562500000000000000 : ℝ)+(6652649276216189/50000000000000000000 : ℝ) ≤ ((13370782235253041707/13375000000000000000 : ℝ)+(443587073053/267500000000000 : ℝ)*((14131/100000 : ℝ)+(358/3125 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (13370782235253041707/13375000000000000000 : ℝ)+(443587073053/267500000000000 : ℝ)*((14131/100000 : ℝ)+(358/3125 : ℝ))=(10001089545025903/10000000000000000 : ℝ) by norm_num, show 1+(493472186162861/1562500000000000000 : ℝ)+(6652649276216189/50000000000000000000 : ℝ)=(50022443759233427741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(493472186162861/1562500000000000000 : ℝ) ≤ ((13370782235253041707/13375000000000000000 : ℝ)+2*(443587073053/267500000000000 : ℝ)*(14131/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (13370782235253041707/13375000000000000000 : ℝ)+2*(443587073053/267500000000000 : ℝ)*(14131/100000 : ℝ)=(2500383283024739/2500000000000000 : ℝ) by norm_num, show 1+2*(493472186162861/1562500000000000000 : ℝ)=(781743472186162861/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13370782235253041707/13375000000000000000 : ℝ)*(X 1 0+X 2 0)+(443587073053/267500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (13370782235253041707/13375000000000000000 : ℝ)) (alpha := (443587073053/267500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13370782235253041707/13375000000000000000 : ℝ)*(X 0 1+X 2 1)+(443587073053/267500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (13370782235253041707/13375000000000000000 : ℝ)) (alpha := (443587073053/267500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13370782235253041707/13375000000000000000 : ℝ)*(X 0 2+X 1 2)+(443587073053/267500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (14131/100000 : ℝ)) (c := (13370782235253041707/13375000000000000000 : ℝ)) (alpha := (443587073053/267500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529756599/2500000000 : ℝ)*X 0 0+(2695676089/5000000000 : ℝ)*X 0 1+(41148901/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133608669/250000000 : ℝ)*X 1 0+(-2182048221/10000000000 : ℝ)*X 1 1+(1316764831/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213773871/400000000 : ℝ)*X 2 0+(2633529659/5000000000 : ℝ)*X 2 1+(-2182048209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350489473/10000000000 : ℝ)*X 0 0+(132067151/312500000 : ℝ)*X 0 1+(4478383029/10000000000 : ℝ)*X 0 2+(4350489473/10000000000 : ℝ)*X 1 0+(132067151/312500000 : ℝ)*X 1 1+(4478383029/10000000000 : ℝ)*X 1 2+(4350489473/10000000000 : ℝ)*X 2 0+(132067151/312500000 : ℝ)*X 2 1+(4478383029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119031009/10000000000 : ℝ)*X 0 0+(658421743/1250000000 : ℝ)*X 0 1+(5391036479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656314293/5000000000 : ℝ)*X 1 0+(-514517673/2500000000 : ℝ)*X 1 1+(5391036813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062525743/2000000000 : ℝ)*X 2 0+(2695518327/5000000000 : ℝ)*X 2 1+(-1029035367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870099763/2000000000 : ℝ)*X 0 0+(4477744919/10000000000 : ℝ)*X 0 1+(1056697363/2500000000 : ℝ)*X 0 2+(870099763/2000000000 : ℝ)*X 1 0+(4477744919/10000000000 : ℝ)*X 1 1+(1056697363/2500000000 : ℝ)*X 1 2+(870099763/2000000000 : ℝ)*X 2 0+(4477744919/10000000000 : ℝ)*X 2 1+(1056697363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2630318468583366472025469357/668750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157266189/20000000000000 : ℝ)*(base19) + (746373433/100000000000000 : ℝ)*(base23) + (6684603/20000000000000 : ℝ)*(lower2) + (47284053/50000000000000 : ℝ)*(upper3) + (72471311/100000000000000 : ℝ)*(upper5) + (6005075313936317/100000000000000 : ℝ)*(major0) + (6005075313936317/100000000000000 : ℝ)*(major1) + (6005075313936317/100000000000000 : ℝ)*(major2) + (502846060940751/6250000000000 : ℝ)*(sp0) + (1609111664034657/20000000000000 : ℝ)*(sp1) + (2011389590032699/25000000000000 : ℝ)*(sp2) + (3964579951073857/100000000000000 : ℝ)*(sp3) + (22131452213/100000000000000 : ℝ)*(sp4) + (11439188321/100000000000000 : ℝ)*(sp7) + (1982295695131089/50000000000000 : ℝ)*(f.failure) + (804555910650423/10000000000000 : ℝ)*(f.sum) + (3184251257331/3343750000000000000000000000 : ℝ)*base66 + (14190580171429476881/1337500000000000000000000000000000 : ℝ)*base68 + (10733543370583023119/1337500000000000000000000000000000 : ℝ)*base69 + (1375790218066976881/1337500000000000000000000000000000 : ℝ)*base72 + (4228643257551/13375000000000000000000000000 : ℝ)*base73 + (29884560866354476881/1337500000000000000000000000000000 : ℝ)*base76 + (27928477269316976881/1337500000000000000000000000000000 : ℝ)*base78 + (11210780850370523119/1337500000000000000000000000000000 : ℝ)*base79 + (4165364877537/6687500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (4531561/2500000000000000000000 : ℝ)*base89 + (4531561/2500000000000000000000 : ℝ)*base91 + (4531561/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2586433324350616201905329031/334375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (634497779/50000000000000 : ℝ)*(base19) + (321447431/20000000000000 : ℝ)*(base23) + (79569487/50000000000000 : ℝ)*(upper3) + (52571711/100000000000000 : ℝ)*(lower4) + (17813327/100000000000000 : ℝ)*(upper5) + (3017822899741289/50000000000000 : ℝ)*(major0) + (3017822899741289/50000000000000 : ℝ)*(major1) + (3017822899741289/50000000000000 : ℝ)*(major2) + (1753912353/3125000000000 : ℝ)*(sp1) + (7914509391/12500000000000 : ℝ)*(sp2) + (1617303421855221/20000000000000 : ℝ)*(sp4) + (32345838860341/400000000000 : ℝ)*(sp5) + (4043226092981911/50000000000000 : ℝ)*(sp6) + (996193557962863/25000000000000 : ℝ)*(sp7) + (996193557962863/25000000000000 : ℝ)*(f.failure) + (1617303421855221/20000000000000 : ℝ)*(f.sum) + (69862015577509/13375000000000000000000000000 : ℝ)*base65 + (2877195345167790323/668750000000000000000000000000000 : ℝ)*base67 + (1776942371811540323/668750000000000000000000000000000 : ℝ)*base69 + (1890086889357209677/668750000000000000000000000000000 : ℝ)*base72 + (3793773739933/6687500000000000000000000000 : ℝ)*base74 + (3139176853605290323/668750000000000000000000000000000 : ℝ)*base75 + (265735584919709677/668750000000000000000000000000000 : ℝ)*base78 + (6447272967642790323/668750000000000000000000000000000 : ℝ)*base79 + (41636137583567/6687500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10950313/1250000000000000000000 : ℝ)*base90 + (10950313/1250000000000000000000 : ℝ)*base92 + (10950313/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1244_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1244_s7_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119040301/10000000000 : ℝ)*x 0 + (5391156437/10000000000 : ℝ)*x 1 + (5267246151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119040301/10000000000 : ℝ)^8437 ≤ (6443213296313/50000000000000 : ℝ)^6389 := by
    have hnat : (2119040301 : ℕ)^8437*50000000000000^6389 ≤ 6443213296313^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119040301 10000000000 6443213296313 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391156437/10000000000 : ℝ)^8437 ≤ (44225456452029/100000000000000 : ℝ)^6389 := by
    have hnat : (5391156437 : ℕ)^8437*100000000000000^6389 ≤ 44225456452029^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391156437 10000000000 44225456452029 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267246151/10000000000 : ℝ)^8437 ≤ (42888116943981/100000000000000 : ℝ)^6389 := by
    have hnat : (5267246151 : ℕ)^8437*100000000000000^6389 ≤ 42888116943981^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267246151 10000000000 42888116943981 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119040301/10000000000 : ℝ), (5391156437/10000000000 : ℝ), (5267246151/10000000000 : ℝ)] ![(6443213296313/50000000000000 : ℝ), (44225456452029/100000000000000 : ℝ), (42888116943981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119040301/10000000000 : ℝ)|^8437 ≤ (6443213296313/50000000000000 : ℝ)^6389
        have hw : |(-2119040301/10000000000 : ℝ)|=(2119040301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391156437/10000000000 : ℝ)|^8437 ≤ (44225456452029/100000000000000 : ℝ)^6389
        have hw : |(5391156437/10000000000 : ℝ)|=(5391156437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267246151/10000000000 : ℝ)|^8437 ≤ (42888116943981/100000000000000 : ℝ)^6389
        have hw : |(5267246151/10000000000 : ℝ)|=(5267246151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s7_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068859581/2000000000 : ℝ)*x 0 + (-2181865317/10000000000 : ℝ)*x 1 + (5267246299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068859581/2000000000 : ℝ)^8437 ≤ (21859275123773/50000000000000 : ℝ)^6389 := by
    have hnat : (1068859581 : ℕ)^8437*50000000000000^6389 ≤ 21859275123773^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068859581 2000000000 21859275123773 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181865317/10000000000 : ℝ)^8437 ≤ (3348332799679/25000000000000 : ℝ)^6389 := by
    have hnat : (2181865317 : ℕ)^8437*25000000000000^6389 ≤ 3348332799679^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181865317 10000000000 3348332799679 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267246299/10000000000 : ℝ)^8437 ≤ (10722029633837/25000000000000 : ℝ)^6389 := by
    have hnat : (5267246299 : ℕ)^8437*25000000000000^6389 ≤ 10722029633837^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267246299 10000000000 10722029633837 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068859581/2000000000 : ℝ), (-2181865317/10000000000 : ℝ), (5267246299/10000000000 : ℝ)] ![(21859275123773/50000000000000 : ℝ), (3348332799679/25000000000000 : ℝ), (10722029633837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068859581/2000000000 : ℝ)|^8437 ≤ (21859275123773/50000000000000 : ℝ)^6389
        have hw : |(1068859581/2000000000 : ℝ)|=(1068859581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181865317/10000000000 : ℝ)|^8437 ≤ (3348332799679/25000000000000 : ℝ)^6389
        have hw : |(-2181865317/10000000000 : ℝ)|=(2181865317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267246299/10000000000 : ℝ)|^8437 ≤ (10722029633837/25000000000000 : ℝ)^6389
        have hw : |(5267246299/10000000000 : ℝ)|=(5267246299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s7_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344297889/10000000000 : ℝ)*x 0 + (1053449259/2000000000 : ℝ)*x 1 + (-17045823/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344297889/10000000000 : ℝ)^8437 ≤ (2732409379669/6250000000000 : ℝ)^6389 := by
    have hnat : (5344297889 : ℕ)^8437*6250000000000^6389 ≤ 2732409379669^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344297889 10000000000 2732409379669 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053449259/2000000000 : ℝ)^8437 ≤ (21444059246169/50000000000000 : ℝ)^6389 := by
    have hnat : (1053449259 : ℕ)^8437*50000000000000^6389 ≤ 21444059246169^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053449259 2000000000 21444059246169 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17045823/78125000 : ℝ)^8437 ≤ (13393331417583/100000000000000 : ℝ)^6389 := by
    have hnat : (17045823 : ℕ)^8437*100000000000000^6389 ≤ 13393331417583^6389*78125000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17045823 78125000 13393331417583 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344297889/10000000000 : ℝ), (1053449259/2000000000 : ℝ), (-17045823/78125000 : ℝ)] ![(2732409379669/6250000000000 : ℝ), (21444059246169/50000000000000 : ℝ), (13393331417583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344297889/10000000000 : ℝ)|^8437 ≤ (2732409379669/6250000000000 : ℝ)^6389
        have hw : |(5344297889/10000000000 : ℝ)|=(5344297889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053449259/2000000000 : ℝ)|^8437 ≤ (21444059246169/50000000000000 : ℝ)^6389
        have hw : |(1053449259/2000000000 : ℝ)|=(1053449259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17045823/78125000 : ℝ)|^8437 ≤ (13393331417583/100000000000000 : ℝ)^6389
        have hw : |(-17045823/78125000 : ℝ)|=(17045823/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s7_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870099859/2000000000 : ℝ)*x 0 + (4226535783/10000000000 : ℝ)*x 1 + (223899673/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870099859/2000000000 : ℝ)^8437 ≤ (16658752427441/50000000000000 : ℝ)^6389 := by
    have hnat : (870099859 : ℕ)^8437*50000000000000^6389 ≤ 16658752427441^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870099859 2000000000 16658752427441 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226535783/10000000000 : ℝ)^8437 ≤ (1002175001177/3125000000000 : ℝ)^6389 := by
    have hnat : (4226535783 : ℕ)^8437*3125000000000^6389 ≤ 1002175001177^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226535783 10000000000 1002175001177 3125000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223899673/500000000 : ℝ)^8437 ≤ (34612895090273/100000000000000 : ℝ)^6389 := by
    have hnat : (223899673 : ℕ)^8437*100000000000000^6389 ≤ 34612895090273^6389*500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223899673 500000000 34612895090273 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870099859/2000000000 : ℝ), (4226535783/10000000000 : ℝ), (223899673/500000000 : ℝ)] ![(16658752427441/50000000000000 : ℝ), (1002175001177/3125000000000 : ℝ), (34612895090273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870099859/2000000000 : ℝ)|^8437 ≤ (16658752427441/50000000000000 : ℝ)^6389
        have hw : |(870099859/2000000000 : ℝ)|=(870099859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226535783/10000000000 : ℝ)|^8437 ≤ (1002175001177/3125000000000 : ℝ)^6389
        have hw : |(4226535783/10000000000 : ℝ)|=(4226535783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(223899673/500000000 : ℝ)|^8437 ≤ (34612895090273/100000000000000 : ℝ)^6389
        have hw : |(223899673/500000000 : ℝ)|=(223899673/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s7_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119044909/10000000000 : ℝ)*x 0 + (2633779401/5000000000 : ℝ)*x 1 + (1078168537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119044909/10000000000 : ℝ)^8437 ≤ (6443231798841/50000000000000 : ℝ)^6389 := by
    have hnat : (2119044909 : ℕ)^8437*50000000000000^6389 ≤ 6443231798841^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119044909 10000000000 6443231798841 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633779401/5000000000 : ℝ)^8437 ≤ (4289147874867/10000000000000 : ℝ)^6389 := by
    have hnat : (2633779401 : ℕ)^8437*10000000000000^6389 ≤ 4289147874867^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633779401 5000000000 4289147874867 10000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078168537/2000000000 : ℝ)^8437 ≤ (442220576333/1000000000000 : ℝ)^6389 := by
    have hnat : (1078168537 : ℕ)^8437*1000000000000^6389 ≤ 442220576333^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078168537 2000000000 442220576333 1000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119044909/10000000000 : ℝ), (2633779401/5000000000 : ℝ), (1078168537/2000000000 : ℝ)] ![(6443231798841/50000000000000 : ℝ), (4289147874867/10000000000000 : ℝ), (442220576333/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119044909/10000000000 : ℝ)|^8437 ≤ (6443231798841/50000000000000 : ℝ)^6389
        have hw : |(-2119044909/10000000000 : ℝ)|=(2119044909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633779401/5000000000 : ℝ)|^8437 ≤ (4289147874867/10000000000000 : ℝ)^6389
        have hw : |(2633779401/5000000000 : ℝ)|=(2633779401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078168537/2000000000 : ℝ)|^8437 ≤ (442220576333/1000000000000 : ℝ)^6389
        have hw : |(1078168537/2000000000 : ℝ)|=(1078168537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s7_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328169297/2500000000 : ℝ)*x 0 + (-2058268993/10000000000 : ℝ)*x 1 + (13477107/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328169297/2500000000 : ℝ)^8437 ≤ (43377287113841/100000000000000 : ℝ)^6389 := by
    have hnat : (1328169297 : ℕ)^8437*100000000000000^6389 ≤ 43377287113841^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328169297 2500000000 43377287113841 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058268993/10000000000 : ℝ)^8437 ≤ (310016349823/2500000000000 : ℝ)^6389 := by
    have hnat : (2058268993 : ℕ)^8437*2500000000000^6389 ≤ 310016349823^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058268993 10000000000 310016349823 2500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13477107/25000000 : ℝ)^8437 ≤ (22111029439531/50000000000000 : ℝ)^6389 := by
    have hnat : (13477107 : ℕ)^8437*50000000000000^6389 ≤ 22111029439531^6389*25000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13477107 25000000 22111029439531 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328169297/2500000000 : ℝ), (-2058268993/10000000000 : ℝ), (13477107/25000000 : ℝ)] ![(43377287113841/100000000000000 : ℝ), (310016349823/2500000000000 : ℝ), (22111029439531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328169297/2500000000 : ℝ)|^8437 ≤ (43377287113841/100000000000000 : ℝ)^6389
        have hw : |(1328169297/2500000000 : ℝ)|=(1328169297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058268993/10000000000 : ℝ)|^8437 ≤ (310016349823/2500000000000 : ℝ)^6389
        have hw : |(-2058268993/10000000000 : ℝ)|=(2058268993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13477107/25000000 : ℝ)|^8437 ≤ (22111029439531/50000000000000 : ℝ)^6389
        have hw : |(13477107/25000000 : ℝ)|=(13477107/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s7_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656338573/5000000000 : ℝ)*x 0 + (5390842869/10000000000 : ℝ)*x 1 + (-514567239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656338573/5000000000 : ℝ)^8437 ≤ (338885052039/781250000000 : ℝ)^6389 := by
    have hnat : (2656338573 : ℕ)^8437*781250000000^6389 ≤ 338885052039^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656338573 5000000000 338885052039 781250000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390842869/10000000000 : ℝ)^8437 ≤ (1105551490663/2500000000000 : ℝ)^6389 := by
    have hnat : (5390842869 : ℕ)^8437*2500000000000^6389 ≤ 1105551490663^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390842869 10000000000 1105551490663 2500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514567239/2500000000 : ℝ)^8437 ≤ (6200326849273/50000000000000 : ℝ)^6389 := by
    have hnat : (514567239 : ℕ)^8437*50000000000000^6389 ≤ 6200326849273^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514567239 2500000000 6200326849273 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656338573/5000000000 : ℝ), (5390842869/10000000000 : ℝ), (-514567239/2500000000 : ℝ)] ![(338885052039/781250000000 : ℝ), (1105551490663/2500000000000 : ℝ), (6200326849273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656338573/5000000000 : ℝ)|^8437 ≤ (338885052039/781250000000 : ℝ)^6389
        have hw : |(2656338573/5000000000 : ℝ)|=(2656338573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390842869/10000000000 : ℝ)|^8437 ≤ (1105551490663/2500000000000 : ℝ)^6389
        have hw : |(5390842869/10000000000 : ℝ)|=(5390842869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-514567239/2500000000 : ℝ)|^8437 ≤ (6200326849273/50000000000000 : ℝ)^6389
        have hw : |(-514567239/2500000000 : ℝ)|=(514567239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s7_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350508561/10000000000 : ℝ)*x 0 + (223867967/500000000 : ℝ)*x 1 + (2113586189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350508561/10000000000 : ℝ)^8437 ≤ (33317598563811/100000000000000 : ℝ)^6389 := by
    have hnat : (4350508561 : ℕ)^8437*100000000000000^6389 ≤ 33317598563811^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350508561 10000000000 33317598563811 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223867967/500000000 : ℝ)^8437 ≤ (34606422602693/100000000000000 : ℝ)^6389 := by
    have hnat : (223867967 : ℕ)^8437*100000000000000^6389 ≤ 34606422602693^6389*500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223867967 500000000 34606422602693 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113586189/5000000000 : ℝ)^8437 ≤ (641519576423/2000000000000 : ℝ)^6389 := by
    have hnat : (2113586189 : ℕ)^8437*2000000000000^6389 ≤ 641519576423^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113586189 5000000000 641519576423 2000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350508561/10000000000 : ℝ), (223867967/500000000 : ℝ), (2113586189/5000000000 : ℝ)] ![(33317598563811/100000000000000 : ℝ), (34606422602693/100000000000000 : ℝ), (641519576423/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350508561/10000000000 : ℝ)|^8437 ≤ (33317598563811/100000000000000 : ℝ)^6389
        have hw : |(4350508561/10000000000 : ℝ)|=(4350508561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223867967/500000000 : ℝ)|^8437 ≤ (34606422602693/100000000000000 : ℝ)^6389
        have hw : |(223867967/500000000 : ℝ)|=(223867967/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113586189/5000000000 : ℝ)|^8437 ≤ (641519576423/2000000000000 : ℝ)^6389
        have hw : |(2113586189/5000000000 : ℝ)|=(2113586189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11481/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7053/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11477/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (6703025887690091/50000000000000000000 : ℝ) := by
    have hpowers : (11477/100000 : ℝ)^2109 ≤ (6703025887690091/50000000000000000000 : ℝ)^512 := by
      have hnat : (11477 : ℕ)^2109*50000000000000000000^512 ≤ 6703025887690091^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11477 100000 6703025887690091 50000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11477/100000 : ℝ)) (X := (6703025887690091/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1411/10000 : ℝ) ^ (2109/512 : ℝ) ≤ (31389339109353299/100000000000000000000 : ℝ) := by
    have hpowers : (1411/10000 : ℝ)^2109 ≤ (31389339109353299/100000000000000000000 : ℝ)^512 := by
      have hnat : (1411 : ℕ)^2109*100000000000000000000^512 ≤ 31389339109353299^512*10000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 10000 31389339109353299 100000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/10000 : ℝ)) (X := (31389339109353299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006703025887690091/25000000000000000000 : ℝ) ≤ (200013016978343/200000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (25006703025887690091/25000000000000000000 : ℝ)^512 ≤ (200013016978343/200000000000000 : ℝ)^2109 := by
      have hnat : (25006703025887690091 : ℕ)^512*200000000000000^2109 ≤ 200013016978343^2109*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006703025887690091 25000000000000000000 200013016978343 200000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200013016978343/200000000000000 : ℝ)) (X := (25006703025887690091/25000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044795390884733481/100000000000000000000 : ℝ) ≤ (10001087309212159/10000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (100044795390884733481/100000000000000000000 : ℝ)^512 ≤ (10001087309212159/10000000000000000 : ℝ)^2109 := by
      have hnat : (100044795390884733481 : ℕ)^512*10000000000000000^2109 ≤ 10001087309212159^2109*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044795390884733481 100000000000000000000 10001087309212159 10000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001087309212159/10000000000000000 : ℝ)) (X := (100044795390884733481/100000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031389339109353299/50000000000000000000 : ℝ) ≤ (312547617797099/312500000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50031389339109353299/50000000000000000000 : ℝ)^512 ≤ (312547617797099/312500000000000 : ℝ)^2109 := by
      have hnat : (50031389339109353299 : ℕ)^512*312500000000000^2109 ≤ 312547617797099^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031389339109353299 50000000000000000000 312547617797099 312500000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312547617797099/312500000000000 : ℝ)) (X := (50031389339109353299/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6703025887690091/50000000000000000000 : ℝ) ≤ ((6580423793896804841/6582500000000000000 : ℝ)+2*(436460295009/263300000000000 : ℝ)*(11477/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (6580423793896804841/6582500000000000000 : ℝ)+2*(436460295009/263300000000000 : ℝ)*(11477/100000 : ℝ)=(200013016978343/200000000000000 : ℝ) by norm_num, show 1+2*(6703025887690091/50000000000000000000 : ℝ)=(25006703025887690091/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31389339109353299/100000000000000000000 : ℝ)+(6703025887690091/50000000000000000000 : ℝ) ≤ ((6580423793896804841/6582500000000000000 : ℝ)+(436460295009/263300000000000 : ℝ)*((1411/10000 : ℝ)+(11477/100000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (6580423793896804841/6582500000000000000 : ℝ)+(436460295009/263300000000000 : ℝ)*((1411/10000 : ℝ)+(11477/100000 : ℝ))=(10001087309212159/10000000000000000 : ℝ) by norm_num, show 1+(31389339109353299/100000000000000000000 : ℝ)+(6703025887690091/50000000000000000000 : ℝ)=(100044795390884733481/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31389339109353299/100000000000000000000 : ℝ) ≤ ((6580423793896804841/6582500000000000000 : ℝ)+2*(436460295009/263300000000000 : ℝ)*(1411/10000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (6580423793896804841/6582500000000000000 : ℝ)+2*(436460295009/263300000000000 : ℝ)*(1411/10000 : ℝ)=(312547617797099/312500000000000 : ℝ) by norm_num, show 1+2*(31389339109353299/100000000000000000000 : ℝ)=(50031389339109353299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6580423793896804841/6582500000000000000 : ℝ)*(X 1 0+X 2 0)+(436460295009/263300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (6580423793896804841/6582500000000000000 : ℝ)) (alpha := (436460295009/263300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6580423793896804841/6582500000000000000 : ℝ)*(X 0 1+X 2 1)+(436460295009/263300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (6580423793896804841/6582500000000000000 : ℝ)) (alpha := (436460295009/263300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6580423793896804841/6582500000000000000 : ℝ)*(X 0 2+X 1 2)+(436460295009/263300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11477/100000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (6580423793896804841/6582500000000000000 : ℝ)) (alpha := (436460295009/263300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2119040301/10000000000 : ℝ)*X 0 0+(5391156437/10000000000 : ℝ)*X 0 1+(5267246151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068859581/2000000000 : ℝ)*X 1 0+(-2181865317/10000000000 : ℝ)*X 1 1+(5267246299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344297889/10000000000 : ℝ)*X 2 0+(1053449259/2000000000 : ℝ)*X 2 1+(-17045823/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870099859/2000000000 : ℝ)*X 0 0+(4226535783/10000000000 : ℝ)*X 0 1+(223899673/500000000 : ℝ)*X 0 2+(870099859/2000000000 : ℝ)*X 1 0+(4226535783/10000000000 : ℝ)*X 1 1+(223899673/500000000 : ℝ)*X 1 2+(870099859/2000000000 : ℝ)*X 2 0+(4226535783/10000000000 : ℝ)*X 2 1+(223899673/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119044909/10000000000 : ℝ)*X 0 0+(2633779401/5000000000 : ℝ)*X 0 1+(1078168537/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328169297/2500000000 : ℝ)*X 1 0+(-2058268993/10000000000 : ℝ)*X 1 1+(13477107/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656338573/5000000000 : ℝ)*X 2 0+(5390842869/10000000000 : ℝ)*X 2 1+(-514567239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350508561/10000000000 : ℝ)*X 0 0+(223867967/500000000 : ℝ)*X 0 1+(2113586189/5000000000 : ℝ)*X 0 2+(4350508561/10000000000 : ℝ)*X 1 0+(223867967/500000000 : ℝ)*X 1 1+(2113586189/5000000000 : ℝ)*X 1 2+(4350508561/10000000000 : ℝ)*X 2 0+(223867967/500000000 : ℝ)*X 2 1+(2113586189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1180966229927181673628745591/329125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (422789207/50000000000000 : ℝ)*(base19) + (653290817/100000000000000 : ℝ)*(base23) + (109704241/100000000000000 : ℝ)*(lower2) + (171924061/100000000000000 : ℝ)*(upper3) + (9926343/50000000000000 : ℝ)*(lower4) + (6023629151463083/100000000000000 : ℝ)*(major0) + (6023629151463083/100000000000000 : ℝ)*(major1) + (6023629151463083/100000000000000 : ℝ)*(major2) + (8070389291240639/100000000000000 : ℝ)*(sp0) + (8070416578292107/100000000000000 : ℝ)*(sp1) + (8070416770579703/100000000000000 : ℝ)*(sp2) + (3976824371426389/100000000000000 : ℝ)*(sp3) + (14066314941/50000000000000 : ℝ)*(sp4) + (4097005647/25000000000000 : ℝ)*(sp7) + (1988420379724489/50000000000000 : ℝ)*(f.failure) + (8070417423870521/100000000000000 : ℝ)*(f.sum) + (28962008355343/13165000000000000000000000000 : ℝ)*base66 + (5749221290154640197/658250000000000000000000000000000 : ℝ)*base68 + (3678577264933890197/658250000000000000000000000000000 : ℝ)*base70 + (2368453741157359803/658250000000000000000000000000000 : ℝ)*base71 + (17543846428273/13165000000000000000000000000 : ℝ)*base74 + (2010665416710609803/658250000000000000000000000000000 : ℝ)*base75 + (16763715663518359803/658250000000000000000000000000000 : ℝ)*base77 + (8317063971476859803/658250000000000000000000000000000 : ℝ)*base79 + (31603813449633/13165000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (36528161/2500000000000000000000 : ℝ)*base89 + (36528161/2500000000000000000000 : ℝ)*base91 + (36528161/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3423538029204701930627743527/329125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212480301/20000000000000 : ℝ)*(base19) + (1354580429/100000000000000 : ℝ)*(base23) + (27712967/12500000000000 : ℝ)*(upper3) + (72066153/50000000000000 : ℝ)*(lower4) + (7395223/6250000000000 : ℝ)*(upper5) + (6054181343224651/100000000000000 : ℝ)*(major0) + (6054181343224651/100000000000000 : ℝ)*(major1) + (6054181343224651/100000000000000 : ℝ)*(major2) + (7307131497/25000000000000 : ℝ)*(sp1) + (4351045387/10000000000000 : ℝ)*(sp2) + (4055675408180153/50000000000000 : ℝ)*(sp4) + (4055660262716407/50000000000000 : ℝ)*(sp5) + (8111305951326007/100000000000000 : ℝ)*(sp6) + (3997011523357707/100000000000000 : ℝ)*(sp7) + (3997011523357707/100000000000000 : ℝ)*(f.failure) + (4055675408180153/50000000000000 : ℝ)*(f.sum) + (29887560457593/6582500000000000000000000000 : ℝ)*base66 + (2226047143404810491/658250000000000000000000000000000 : ℝ)*base67 + (1948134687723189509/658250000000000000000000000000000 : ℝ)*base70 + (340434062547060491/658250000000000000000000000000000 : ℝ)*base71 + (32955302685329/13165000000000000000000000000 : ℝ)*base73 + (2113599568960310491/658250000000000000000000000000000 : ℝ)*base75 + (2283557312262939509/658250000000000000000000000000000 : ℝ)*base78 + (1579387398106560491/658250000000000000000000000000000 : ℝ)*base79 + (26951482045351/13165000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4924243/5000000000000000000000 : ℝ)*base89 + (4924243/5000000000000000000000 : ℝ)*base91 + (4924243/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1244_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1244_s8_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-264880349/1250000000 : ℝ)*x 0 + (2695559629/5000000000 : ℝ)*x 1 + (1316820437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264880349/1250000000 : ℝ)^8437 ≤ (4123662911/32000000000 : ℝ)^6389 := by
    have hnat : (264880349 : ℕ)^8437*32000000000^6389 ≤ 4123662911^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264880349 1250000000 4123662911 32000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695559629/5000000000 : ℝ)^8437 ≤ (44225053695327/100000000000000 : ℝ)^6389 := by
    have hnat : (2695559629 : ℕ)^8437*100000000000000^6389 ≤ 44225053695327^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695559629 5000000000 44225053695327 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316820437/2500000000 : ℝ)^8437 ≤ (21444249850161/50000000000000 : ℝ)^6389 := by
    have hnat : (1316820437 : ℕ)^8437*50000000000000^6389 ≤ 21444249850161^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316820437 2500000000 21444249850161 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264880349/1250000000 : ℝ), (2695559629/5000000000 : ℝ), (1316820437/2500000000 : ℝ)] ![(4123662911/32000000000 : ℝ), (44225053695327/100000000000000 : ℝ), (21444249850161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264880349/1250000000 : ℝ)|^8437 ≤ (4123662911/32000000000 : ℝ)^6389
        have hw : |(-264880349/1250000000 : ℝ)|=(264880349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695559629/5000000000 : ℝ)|^8437 ≤ (44225053695327/100000000000000 : ℝ)^6389
        have hw : |(2695559629/5000000000 : ℝ)|=(2695559629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316820437/2500000000 : ℝ)|^8437 ≤ (21444249850161/50000000000000 : ℝ)^6389
        have hw : |(1316820437/2500000000 : ℝ)|=(1316820437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s8_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068857749/2000000000 : ℝ)*x 0 + (-545457741/2500000000 : ℝ)*x 1 + (5267281401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068857749/2000000000 : ℝ)^8437 ≤ (43718451295311/100000000000000 : ℝ)^6389 := by
    have hnat : (1068857749 : ℕ)^8437*100000000000000^6389 ≤ 43718451295311^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068857749 2000000000 43718451295311 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545457741/2500000000 : ℝ)^8437 ≤ (6696526364041/50000000000000 : ℝ)^6389 := by
    have hnat : (545457741 : ℕ)^8437*50000000000000^6389 ≤ 6696526364041^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545457741 2500000000 6696526364041 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267281401/10000000000 : ℝ)^8437 ≤ (10722123992301/25000000000000 : ℝ)^6389 := by
    have hnat : (5267281401 : ℕ)^8437*25000000000000^6389 ≤ 10722123992301^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267281401 10000000000 10722123992301 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068857749/2000000000 : ℝ), (-545457741/2500000000 : ℝ), (5267281401/10000000000 : ℝ)] ![(43718451295311/100000000000000 : ℝ), (6696526364041/50000000000000 : ℝ), (10722123992301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068857749/2000000000 : ℝ)|^8437 ≤ (43718451295311/100000000000000 : ℝ)^6389
        have hw : |(1068857749/2000000000 : ℝ)|=(1068857749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545457741/2500000000 : ℝ)|^8437 ≤ (6696526364041/50000000000000 : ℝ)^6389
        have hw : |(-545457741/2500000000 : ℝ)|=(545457741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267281401/10000000000 : ℝ)|^8437 ≤ (10722123992301/25000000000000 : ℝ)^6389
        have hw : |(5267281401/10000000000 : ℝ)|=(5267281401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s8_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-52976191/250000000 : ℝ)*x 0 + (1316898329/2500000000 : ℝ)*x 1 + (2695403201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52976191/250000000 : ℝ)^8437 ≤ (6443242764647/50000000000000 : ℝ)^6389 := by
    have hnat : (52976191 : ℕ)^8437*50000000000000^6389 ≤ 6443242764647^6389*250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52976191 250000000 6443242764647 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316898329/2500000000 : ℝ)^8437 ≤ (8578369973423/20000000000000 : ℝ)^6389 := by
    have hnat : (1316898329 : ℕ)^8437*20000000000000^6389 ≤ 8578369973423^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316898329 2500000000 8578369973423 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695403201/5000000000 : ℝ)^8437 ≤ (22110832295103/50000000000000 : ℝ)^6389 := by
    have hnat : (2695403201 : ℕ)^8437*50000000000000^6389 ≤ 22110832295103^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695403201 5000000000 22110832295103 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52976191/250000000 : ℝ), (1316898329/2500000000 : ℝ), (2695403201/5000000000 : ℝ)] ![(6443242764647/50000000000000 : ℝ), (8578369973423/20000000000000 : ℝ), (22110832295103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52976191/250000000 : ℝ)|^8437 ≤ (6443242764647/50000000000000 : ℝ)^6389
        have hw : |(-52976191/250000000 : ℝ)|=(52976191/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316898329/2500000000 : ℝ)|^8437 ≤ (8578369973423/20000000000000 : ℝ)^6389
        have hw : |(1316898329/2500000000 : ℝ)|=(1316898329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695403201/5000000000 : ℝ)|^8437 ≤ (22110832295103/50000000000000 : ℝ)^6389
        have hw : |(2695403201/5000000000 : ℝ)|=(2695403201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s8_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312686761/10000000000 : ℝ)*x 0 + (-2058306421/10000000000 : ℝ)*x 1 + (5390805783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312686761/10000000000 : ℝ)^8437 ≤ (5422173791387/12500000000000 : ℝ)^6389 := by
    have hnat : (5312686761 : ℕ)^8437*12500000000000^6389 ≤ 5422173791387^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312686761 10000000000 5422173791387 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058306421/10000000000 : ℝ)^8437 ≤ (6200475886453/50000000000000 : ℝ)^6389 := by
    have hnat : (2058306421 : ℕ)^8437*50000000000000^6389 ≤ 6200475886453^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058306421 10000000000 6200475886453 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390805783/10000000000 : ℝ)^8437 ≤ (1381926808899/3125000000000 : ℝ)^6389 := by
    have hnat : (5390805783 : ℕ)^8437*3125000000000^6389 ≤ 1381926808899^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390805783 10000000000 1381926808899 3125000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312686761/10000000000 : ℝ), (-2058306421/10000000000 : ℝ), (5390805783/10000000000 : ℝ)] ![(5422173791387/12500000000000 : ℝ), (6200475886453/50000000000000 : ℝ), (1381926808899/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312686761/10000000000 : ℝ)|^8437 ≤ (5422173791387/12500000000000 : ℝ)^6389
        have hw : |(5312686761/10000000000 : ℝ)|=(5312686761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058306421/10000000000 : ℝ)|^8437 ≤ (6200475886453/50000000000000 : ℝ)^6389
        have hw : |(-2058306421/10000000000 : ℝ)|=(2058306421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390805783/10000000000 : ℝ)|^8437 ≤ (1381926808899/3125000000000 : ℝ)^6389
        have hw : |(5390805783/10000000000 : ℝ)|=(5390805783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s8_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656343211/5000000000 : ℝ)*x 0 + (1078161247/2000000000 : ℝ)*x 1 + (-257288283/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656343211/5000000000 : ℝ)^8437 ≤ (8675477335191/20000000000000 : ℝ)^6389 := by
    have hnat : (2656343211 : ℕ)^8437*20000000000000^6389 ≤ 8675477335191^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656343211 5000000000 8675477335191 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078161247/2000000000 : ℝ)^8437 ≤ (22110831390573/50000000000000 : ℝ)^6389 := by
    have hnat : (1078161247 : ℕ)^8437*50000000000000^6389 ≤ 22110831390573^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078161247 2000000000 22110831390573 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257288283/1250000000 : ℝ)^8437 ≤ (6200475261899/50000000000000 : ℝ)^6389 := by
    have hnat : (257288283 : ℕ)^8437*50000000000000^6389 ≤ 6200475261899^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257288283 1250000000 6200475261899 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656343211/5000000000 : ℝ), (1078161247/2000000000 : ℝ), (-257288283/1250000000 : ℝ)] ![(8675477335191/20000000000000 : ℝ), (22110831390573/50000000000000 : ℝ), (6200475261899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656343211/5000000000 : ℝ)|^8437 ≤ (8675477335191/20000000000000 : ℝ)^6389
        have hw : |(2656343211/5000000000 : ℝ)|=(2656343211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078161247/2000000000 : ℝ)|^8437 ≤ (22110831390573/50000000000000 : ℝ)^6389
        have hw : |(1078161247/2000000000 : ℝ)|=(1078161247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257288283/1250000000 : ℝ)|^8437 ≤ (6200475261899/50000000000000 : ℝ)^6389
        have hw : |(-257288283/1250000000 : ℝ)|=(257288283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s8_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350510471/10000000000 : ℝ)*x 0 + (2238643103/5000000000 : ℝ)*x 1 + (264202809/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350510471/10000000000 : ℝ)^8437 ≤ (16658808940017/50000000000000 : ℝ)^6389 := by
    have hnat : (4350510471 : ℕ)^8437*50000000000000^6389 ≤ 16658808940017^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350510471 10000000000 16658808940017 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238643103/5000000000 : ℝ)^8437 ≤ (1730283807/5000000000 : ℝ)^6389 := by
    have hnat : (2238643103 : ℕ)^8437*5000000000^6389 ≤ 1730283807^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238643103 5000000000 1730283807 5000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264202809/625000000 : ℝ)^8437 ≤ (16038352981801/50000000000000 : ℝ)^6389 := by
    have hnat : (264202809 : ℕ)^8437*50000000000000^6389 ≤ 16038352981801^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264202809 625000000 16038352981801 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350510471/10000000000 : ℝ), (2238643103/5000000000 : ℝ), (264202809/625000000 : ℝ)] ![(16658808940017/50000000000000 : ℝ), (1730283807/5000000000 : ℝ), (16038352981801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350510471/10000000000 : ℝ)|^8437 ≤ (16658808940017/50000000000000 : ℝ)^6389
        have hw : |(4350510471/10000000000 : ℝ)|=(4350510471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238643103/5000000000 : ℝ)|^8437 ≤ (1730283807/5000000000 : ℝ)^6389
        have hw : |(2238643103/5000000000 : ℝ)|=(2238643103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264202809/625000000 : ℝ)|^8437 ≤ (16038352981801/50000000000000 : ℝ)^6389
        have hw : |(264202809/625000000 : ℝ)|=(264202809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11481/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2821/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11481/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (13425308178717369/100000000000000000000 : ℝ) := by
    have hpowers : (11481/100000 : ℝ)^2109 ≤ (13425308178717369/100000000000000000000 : ℝ)^512 := by
      have hnat : (11481 : ℕ)^2109*100000000000000000000^512 ≤ 13425308178717369^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11481 100000 13425308178717369 100000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11481/100000 : ℝ)) (X := (13425308178717369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7053/50000 : ℝ) ^ (2109/512 : ℝ) ≤ (6270540255672413/20000000000000000000 : ℝ) := by
    have hpowers : (7053/50000 : ℝ)^2109 ≤ (6270540255672413/20000000000000000000 : ℝ)^512 := by
      have hnat : (7053 : ℕ)^2109*20000000000000000000^512 ≤ 6270540255672413^512*50000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7053 50000 6270540255672413 20000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7053/50000 : ℝ)) (X := (6270540255672413/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013425308178717369/50000000000000000000 : ℝ) ≤ (5000325891849557/5000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50013425308178717369/50000000000000000000 : ℝ)^512 ≤ (5000325891849557/5000000000000000 : ℝ)^2109 := by
      have hnat : (50013425308178717369 : ℕ)^512*5000000000000000^2109 ≤ 5000325891849557^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013425308178717369 50000000000000000000 5000325891849557 5000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000325891849557/5000000000000000 : ℝ)) (X := (50013425308178717369/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022389004728539717/50000000000000000000 : ℝ) ≤ (250027172184697/250000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50022389004728539717/50000000000000000000 : ℝ)^512 ≤ (250027172184697/250000000000000 : ℝ)^2109 := by
      have hnat : (50022389004728539717 : ℕ)^512*250000000000000^2109 ≤ 250027172184697^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022389004728539717 50000000000000000000 250027172184697 250000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250027172184697/250000000000000 : ℝ)) (X := (50022389004728539717/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006270540255672413/10000000000000000000 : ℝ) ≤ (5000760995538323/5000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (10006270540255672413/10000000000000000000 : ℝ)^512 ≤ (5000760995538323/5000000000000000 : ℝ)^2109 := by
      have hnat : (10006270540255672413 : ℕ)^512*5000000000000000^2109 ≤ 5000760995538323^2109*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006270540255672413 10000000000000000000 5000760995538323 5000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000760995538323/5000000000000000 : ℝ)) (X := (10006270540255672413/10000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13425308178717369/100000000000000000000 : ℝ) ≤ ((4373620013551454893/4375000000000000000 : ℝ)+2*(72517281461/43750000000000 : ℝ)*(11481/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (4373620013551454893/4375000000000000000 : ℝ)+2*(72517281461/43750000000000 : ℝ)*(11481/100000 : ℝ)=(5000325891849557/5000000000000000 : ℝ) by norm_num, show 1+2*(13425308178717369/100000000000000000000 : ℝ)=(50013425308178717369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6270540255672413/20000000000000000000 : ℝ)+(13425308178717369/100000000000000000000 : ℝ) ≤ ((4373620013551454893/4375000000000000000 : ℝ)+(72517281461/43750000000000 : ℝ)*((7053/50000 : ℝ)+(11481/100000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (4373620013551454893/4375000000000000000 : ℝ)+(72517281461/43750000000000 : ℝ)*((7053/50000 : ℝ)+(11481/100000 : ℝ))=(250027172184697/250000000000000 : ℝ) by norm_num, show 1+(6270540255672413/20000000000000000000 : ℝ)+(13425308178717369/100000000000000000000 : ℝ)=(50022389004728539717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6270540255672413/20000000000000000000 : ℝ) ≤ ((4373620013551454893/4375000000000000000 : ℝ)+2*(72517281461/43750000000000 : ℝ)*(7053/50000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (4373620013551454893/4375000000000000000 : ℝ)+2*(72517281461/43750000000000 : ℝ)*(7053/50000 : ℝ)=(5000760995538323/5000000000000000 : ℝ) by norm_num, show 1+2*(6270540255672413/20000000000000000000 : ℝ)=(10006270540255672413/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4373620013551454893/4375000000000000000 : ℝ)*(X 1 0+X 2 0)+(72517281461/43750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (4373620013551454893/4375000000000000000 : ℝ)) (alpha := (72517281461/43750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4373620013551454893/4375000000000000000 : ℝ)*(X 0 1+X 2 1)+(72517281461/43750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (4373620013551454893/4375000000000000000 : ℝ)) (alpha := (72517281461/43750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4373620013551454893/4375000000000000000 : ℝ)*(X 0 2+X 1 2)+(72517281461/43750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (4373620013551454893/4375000000000000000 : ℝ)) (alpha := (72517281461/43750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-264880349/1250000000 : ℝ)*X 0 0+(2695559629/5000000000 : ℝ)*X 0 1+(1316820437/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068857749/2000000000 : ℝ)*X 1 0+(-545457741/2500000000 : ℝ)*X 1 1+(5267281401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-52976191/250000000 : ℝ)*X 0 0+(1316898329/2500000000 : ℝ)*X 0 1+(2695403201/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s8_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312686761/10000000000 : ℝ)*X 1 0+(-2058306421/10000000000 : ℝ)*X 1 1+(5390805783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s8_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2656343211/5000000000 : ℝ)*X 2 0+(1078161247/2000000000 : ℝ)*X 2 1+(-257288283/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s8_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4350510471/10000000000 : ℝ)*X 0 0+(2238643103/5000000000 : ℝ)*X 0 1+(264202809/625000000 : ℝ)*X 0 2+(4350510471/10000000000 : ℝ)*X 1 0+(2238643103/5000000000 : ℝ)*X 1 1+(264202809/625000000 : ℝ)*X 1 2+(4350510471/10000000000 : ℝ)*X 2 0+(2238643103/5000000000 : ℝ)*X 2 1+(264202809/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164610094987066981633163817/27343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101486389/6250000000000 : ℝ)*(base19) + (306519971/25000000000000 : ℝ)*(base23) + (102152037/25000000000000 : ℝ)*(lower1) + (33758013/50000000000000 : ℝ)*(lower4) + (291095663/100000000000000 : ℝ)*(upper5) + (757208668788441/12500000000000 : ℝ)*(major0) + (757208668788441/12500000000000 : ℝ)*(major1) + (757208668788441/12500000000000 : ℝ)*(major2) + (7160555027/50000000000000 : ℝ)*(sp0) + (1161206739/100000000000000 : ℝ)*(sp1) + (8116009849581891/100000000000000 : ℝ)*(sp2) + (8116021385702983/100000000000000 : ℝ)*(sp3) + (8116022944612061/100000000000000 : ℝ)*(sp4) + (1999657164627777/50000000000000 : ℝ)*(sp5) + (1999657164627777/50000000000000 : ℝ)*(f.failure) + (1623204834138389/20000000000000 : ℝ)*(f.sum) + (10315097050283/2187500000000000000000000000 : ℝ)*base65 + (555226952817358187/54687500000000000000000000000000 : ℝ)*base68 + (886448957239233187/54687500000000000000000000000000 : ℝ)*base70 + (319672465161108187/54687500000000000000000000000000 : ℝ)*base72 + (7174969279941/4375000000000000000000000000 : ℝ)*base73 + (1967497864879858187/54687500000000000000000000000000 : ℝ)*base76 + (112624229754858187/54687500000000000000000000000000 : ℝ)*base78 + (1955879913200170687/54687500000000000000000000000000 : ℝ)*base80 + (1189184067273/546875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4523673/2500000000000000000000 : ℝ)*base89 + (4523673/2500000000000000000000 : ℝ)*base91 + (4523673/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1244_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1244_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1244_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1244_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1244_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1244_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
