-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1773_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:34:39.863601+00:00
-- url     : https://prove2.me/submissions/ced409b9-2432-4127-b260-b000814a73e3

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
theorem support_rectangle_w1773_s3_0 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2115431/4000000 : ℝ)*x 0 + (5229270179/10000000000 : ℝ)*x 1 + (-288960513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115431/4000000 : ℝ)^6 ≤ (46559322012791/100000000000000 : ℝ)^5 := by
    have hnat : (2115431 : ℕ)^6*100000000000000^5 ≤ 46559322012791^5*4000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115431 4000000 46559322012791 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229270179/10000000000 : ℝ)^6 ≤ (22966737228231/50000000000000 : ℝ)^5 := by
    have hnat : (5229270179 : ℕ)^6*50000000000000^5 ≤ 22966737228231^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229270179 10000000000 22966737228231 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (288960513/2500000000 : ℝ)^6 ≤ (938400438791/12500000000000 : ℝ)^5 := by
    have hnat : (288960513 : ℕ)^6*12500000000000^5 ≤ 938400438791^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288960513 2500000000 938400438791 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2115431/4000000 : ℝ), (5229270179/10000000000 : ℝ), (-288960513/2500000000 : ℝ)] ![(46559322012791/100000000000000 : ℝ), (22966737228231/50000000000000 : ℝ), (938400438791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2115431/4000000 : ℝ)|^6 ≤ (46559322012791/100000000000000 : ℝ)^5
        have hw : |(2115431/4000000 : ℝ)|=(2115431/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229270179/10000000000 : ℝ)|^6 ≤ (22966737228231/50000000000000 : ℝ)^5
        have hw : |(5229270179/10000000000 : ℝ)|=(5229270179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-288960513/2500000000 : ℝ)|^6 ≤ (938400438791/12500000000000 : ℝ)^5
        have hw : |(-288960513/2500000000 : ℝ)|=(288960513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s3_1 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-554102319/5000000000 : ℝ)*x 0 + (2614840093/5000000000 : ℝ)*x 1 + (5323144113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554102319/5000000000 : ℝ)^6 ≤ (7137464416383/100000000000000 : ℝ)^5 := by
    have hnat : (554102319 : ℕ)^6*100000000000000^5 ≤ 7137464416383^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554102319 5000000000 7137464416383 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614840093/5000000000 : ℝ)^6 ≤ (5742224531403/12500000000000 : ℝ)^5 := by
    have hnat : (2614840093 : ℕ)^6*12500000000000^5 ≤ 5742224531403^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614840093 5000000000 5742224531403 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5323144113/10000000000 : ℝ)^6 ≤ (11731184831713/25000000000000 : ℝ)^5 := by
    have hnat : (5323144113 : ℕ)^6*25000000000000^5 ≤ 11731184831713^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5323144113 10000000000 11731184831713 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-554102319/5000000000 : ℝ), (2614840093/5000000000 : ℝ), (5323144113/10000000000 : ℝ)] ![(7137464416383/100000000000000 : ℝ), (5742224531403/12500000000000 : ℝ), (11731184831713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-554102319/5000000000 : ℝ)|^6 ≤ (7137464416383/100000000000000 : ℝ)^5
        have hw : |(-554102319/5000000000 : ℝ)|=(554102319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614840093/5000000000 : ℝ)|^6 ≤ (5742224531403/12500000000000 : ℝ)^5
        have hw : |(2614840093/5000000000 : ℝ)|=(2614840093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5323144113/10000000000 : ℝ)|^6 ≤ (11731184831713/25000000000000 : ℝ)^5
        have hw : |(5323144113/10000000000 : ℝ)|=(5323144113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s3_2 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2631708309/5000000000 : ℝ)*x 0 + (-1061968119/10000000000 : ℝ)*x 1 + (166348251/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631708309/5000000000 : ℝ)^6 ≤ (46293636453419/100000000000000 : ℝ)^5 := by
    have hnat : (2631708309 : ℕ)^6*100000000000000^5 ≤ 46293636453419^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631708309 5000000000 46293636453419 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061968119/10000000000 : ℝ)^6 ≤ (6781625059397/100000000000000 : ℝ)^5 := by
    have hnat : (1061968119 : ℕ)^6*100000000000000^5 ≤ 6781625059397^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061968119 10000000000 6781625059397 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166348251/312500000 : ℝ)^6 ≤ (11731184617503/25000000000000 : ℝ)^5 := by
    have hnat : (166348251 : ℕ)^6*25000000000000^5 ≤ 11731184617503^5*312500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166348251 312500000 11731184617503 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631708309/5000000000 : ℝ), (-1061968119/10000000000 : ℝ), (166348251/312500000 : ℝ)] ![(46293636453419/100000000000000 : ℝ), (6781625059397/100000000000000 : ℝ), (11731184617503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631708309/5000000000 : ℝ)|^6 ≤ (46293636453419/100000000000000 : ℝ)^5
        have hw : |(2631708309/5000000000 : ℝ)|=(2631708309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061968119/10000000000 : ℝ)|^6 ≤ (6781625059397/100000000000000 : ℝ)^5
        have hw : |(-1061968119/10000000000 : ℝ)|=(1061968119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166348251/312500000 : ℝ)|^6 ≤ (11731184617503/25000000000000 : ℝ)^5
        have hw : |(166348251/312500000 : ℝ)|=(166348251/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s3_3 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5263416589/10000000000 : ℝ)*x 0 + (532314409/1000000000 : ℝ)*x 1 + (-13274601/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263416589/10000000000 : ℝ)^6 ≤ (46293636147341/100000000000000 : ℝ)^5 := by
    have hnat : (5263416589 : ℕ)^6*100000000000000^5 ≤ 46293636147341^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263416589 10000000000 46293636147341 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532314409/1000000000 : ℝ)^6 ≤ (1466398096361/3125000000000 : ℝ)^5 := by
    have hnat : (532314409 : ℕ)^6*3125000000000^5 ≤ 1466398096361^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532314409 1000000000 1466398096361 3125000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13274601/125000000 : ℝ)^6 ≤ (6781624760537/100000000000000 : ℝ)^5 := by
    have hnat : (13274601 : ℕ)^6*100000000000000^5 ≤ 6781624760537^5*125000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13274601 125000000 6781624760537 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263416589/10000000000 : ℝ), (532314409/1000000000 : ℝ), (-13274601/125000000 : ℝ)] ![(46293636147341/100000000000000 : ℝ), (1466398096361/3125000000000 : ℝ), (6781624760537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263416589/10000000000 : ℝ)|^6 ≤ (46293636147341/100000000000000 : ℝ)^5
        have hw : |(5263416589/10000000000 : ℝ)|=(5263416589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(532314409/1000000000 : ℝ)|^6 ≤ (1466398096361/3125000000000 : ℝ)^5
        have hw : |(532314409/1000000000 : ℝ)|=(532314409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13274601/125000000 : ℝ)|^6 ≤ (6781624760537/100000000000000 : ℝ)^5
        have hw : |(-13274601/125000000 : ℝ)|=(13274601/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_s3_4 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2000728771/5000000000 : ℝ)*x 0 + (834379397/2000000000 : ℝ)*x 1 + (1917296813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000728771/5000000000 : ℝ)^6 ≤ (16658345300919/50000000000000 : ℝ)^5 := by
    have hnat : (2000728771 : ℕ)^6*50000000000000^5 ≤ 16658345300919^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000728771 5000000000 16658345300919 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834379397/2000000000 : ℝ)^6 ≤ (1401071447189/4000000000000 : ℝ)^5 := by
    have hnat : (834379397 : ℕ)^6*4000000000000^5 ≤ 1401071447189^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834379397 2000000000 1401071447189 4000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1917296813/5000000000 : ℝ)^6 ≤ (31656523211939/100000000000000 : ℝ)^5 := by
    have hnat : (1917296813 : ℕ)^6*100000000000000^5 ≤ 31656523211939^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917296813 5000000000 31656523211939 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2000728771/5000000000 : ℝ), (834379397/2000000000 : ℝ), (1917296813/5000000000 : ℝ)] ![(16658345300919/50000000000000 : ℝ), (1401071447189/4000000000000 : ℝ), (31656523211939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2000728771/5000000000 : ℝ)|^6 ≤ (16658345300919/50000000000000 : ℝ)^5
        have hw : |(2000728771/5000000000 : ℝ)|=(2000728771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834379397/2000000000 : ℝ)|^6 ≤ (1401071447189/4000000000000 : ℝ)^5
        have hw : |(834379397/2000000000 : ℝ)|=(834379397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1917296813/5000000000 : ℝ)|^6 ≤ (31656523211939/100000000000000 : ℝ)^5
        have hw : |(1917296813/5000000000 : ℝ)|=(1917296813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1773_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3609/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (12371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2887/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3609/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (12371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3609/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (12371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3609/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (12371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3609/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (12371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3609/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (12371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3609/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (12371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (12371/100000 : ℝ) ^ (6143/1024 : ℝ) ≤ (359182496610181/100000000000000000000 : ℝ) := by
    have hpowers : (12371/100000 : ℝ)^6143 ≤ (359182496610181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12371 : ℕ)^6143*100000000000000000000^1024 ≤ 359182496610181^1024*100000^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12371 100000 359182496610181 100000000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12371/100000 : ℝ)) (X := (359182496610181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3609/25000 : ℝ) ^ (6143/1024 : ℝ) ≤ (453390167301703/50000000000000000000 : ℝ) := by
    have hpowers : (3609/25000 : ℝ)^6143 ≤ (453390167301703/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3609 : ℕ)^6143*50000000000000000000^1024 ≤ 453390167301703^1024*25000^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3609 25000 453390167301703 50000000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3609/25000 : ℝ)) (X := (453390167301703/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000359182496610181/50000000000000000000 : ℝ) ≤ (10000011974663053/10000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (50000359182496610181/50000000000000000000 : ℝ)^1024 ≤ (10000011974663053/10000000000000000 : ℝ)^6143 := by
      have hnat : (50000359182496610181 : ℕ)^1024*10000000000000000^6143 ≤ 10000011974663053^6143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000359182496610181 50000000000000000000 10000011974663053 10000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000011974663053/10000000000000000 : ℝ)) (X := (50000359182496610181/50000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100001265962831213587/100000000000000000000 : ℝ) ≤ (5000010551351957/5000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (100001265962831213587/100000000000000000000 : ℝ)^1024 ≤ (5000010551351957/5000000000000000 : ℝ)^6143 := by
      have hnat : (100001265962831213587 : ℕ)^1024*5000000000000000^6143 ≤ 5000010551351957^6143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100001265962831213587 100000000000000000000 5000010551351957 5000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000010551351957/5000000000000000 : ℝ)) (X := (100001265962831213587/100000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25000453390167301703/25000000000000000000 : ℝ) ≤ (400001209229791/400000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (25000453390167301703/25000000000000000000 : ℝ)^1024 ≤ (400001209229791/400000000000000 : ℝ)^6143 := by
      have hnat : (25000453390167301703 : ℕ)^1024*400000000000000^6143 ≤ 400001209229791^6143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000453390167301703 25000000000000000000 400001209229791 400000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400001209229791/400000000000000 : ℝ)) (X := (25000453390167301703/25000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(359182496610181/100000000000000000000 : ℝ) ≤ ((20649798881692221583/20650000000000000000 : ℝ)+2*(9128040861/206500000000000 : ℝ)*(12371/100000 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (20649798881692221583/20650000000000000000 : ℝ)+2*(9128040861/206500000000000 : ℝ)*(12371/100000 : ℝ)=(10000011974663053/10000000000000000 : ℝ) by norm_num, show 1+2*(359182496610181/100000000000000000000 : ℝ)=(50000359182496610181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(453390167301703/50000000000000000000 : ℝ)+(359182496610181/100000000000000000000 : ℝ) ≤ ((20649798881692221583/20650000000000000000 : ℝ)+(9128040861/206500000000000 : ℝ)*((3609/25000 : ℝ)+(12371/100000 : ℝ)))^(6143/1024 : ℝ) := by
    rw [show (20649798881692221583/20650000000000000000 : ℝ)+(9128040861/206500000000000 : ℝ)*((3609/25000 : ℝ)+(12371/100000 : ℝ))=(5000010551351957/5000000000000000 : ℝ) by norm_num, show 1+(453390167301703/50000000000000000000 : ℝ)+(359182496610181/100000000000000000000 : ℝ)=(100001265962831213587/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(453390167301703/50000000000000000000 : ℝ) ≤ ((20649798881692221583/20650000000000000000 : ℝ)+2*(9128040861/206500000000000 : ℝ)*(3609/25000 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (20649798881692221583/20650000000000000000 : ℝ)+2*(9128040861/206500000000000 : ℝ)*(3609/25000 : ℝ)=(400001209229791/400000000000000 : ℝ) by norm_num, show 1+2*(453390167301703/50000000000000000000 : ℝ)=(25000453390167301703/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20649798881692221583/20650000000000000000 : ℝ)*(X 1 0+X 2 0)+(9128040861/206500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12371/100000 : ℝ)) (hi := (3609/25000 : ℝ)) (c := (20649798881692221583/20650000000000000000 : ℝ)) (alpha := (9128040861/206500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20649798881692221583/20650000000000000000 : ℝ)*(X 0 1+X 2 1)+(9128040861/206500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12371/100000 : ℝ)) (hi := (3609/25000 : ℝ)) (c := (20649798881692221583/20650000000000000000 : ℝ)) (alpha := (9128040861/206500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20649798881692221583/20650000000000000000 : ℝ)*(X 0 2+X 1 2)+(9128040861/206500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12371/100000 : ℝ)) (hi := (3609/25000 : ℝ)) (c := (20649798881692221583/20650000000000000000 : ℝ)) (alpha := (9128040861/206500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2115431/4000000 : ℝ)*X 2 0+(5229270179/10000000000 : ℝ)*X 2 1+(-288960513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s3_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-554102319/5000000000 : ℝ)*X 0 0+(2614840093/5000000000 : ℝ)*X 0 1+(5323144113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s3_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2631708309/5000000000 : ℝ)*X 1 0+(-1061968119/10000000000 : ℝ)*X 1 1+(166348251/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s3_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5263416589/10000000000 : ℝ)*X 2 0+(532314409/1000000000 : ℝ)*X 2 1+(-13274601/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s3_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2000728771/5000000000 : ℝ)*X 0 0+(834379397/2000000000 : ℝ)*X 0 1+(1917296813/5000000000 : ℝ)*X 0 2+(2000728771/5000000000 : ℝ)*X 1 0+(834379397/2000000000 : ℝ)*X 1 1+(1917296813/5000000000 : ℝ)*X 1 2+(2000728771/5000000000 : ℝ)*X 2 0+(834379397/2000000000 : ℝ)*X 2 1+(1917296813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_s3_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8370529365305982381670758807/1032500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (506674949/50000000000000 : ℝ)*(base19) + (211287123/20000000000000 : ℝ)*(base23) + (268900479/100000000000000 : ℝ)*(lower1) + (59182217/50000000000000 : ℝ)*(upper3) + (47483799/100000000000000 : ℝ)*(lower4) + (25928683/12500000000000 : ℝ)*(upper5) + (6831985070475443/100000000000000 : ℝ)*(major0) + (6831985070475443/100000000000000 : ℝ)*(major1) + (6831985070475443/100000000000000 : ℝ)*(major2) + (2472859171/100000000000000 : ℝ)*(sp0) + (213985789772793/2000000000000 : ℝ)*(sp1) + (1337411059411219/12500000000000 : ℝ)*(sp2) + (334352686229527/3125000000000 : ℝ)*(sp3) + (185292523879763/6250000000000 : ℝ)*(sp4) + (185292523879763/6250000000000 : ℝ)*(f.failure) + (213985789772793/2000000000000 : ℝ)*(f.sum) + (334130095277/10325000000000000000000000000 : ℝ)*base66 + (28486459797341613731/2065000000000000000000000000000000 : ℝ)*base68 + (40173168040411613731/2065000000000000000000000000000000 : ℝ)*base70 + (166348238041321613731/2065000000000000000000000000000000 : ℝ)*base72 + (14075931829023/10325000000000000000000000000 : ℝ)*base73 + (84648483556678386269/2065000000000000000000000000000000 : ℝ)*base75 + (34450292034221613731/2065000000000000000000000000000000 : ℝ)*base78 + (26955815634173386269/2065000000000000000000000000000000 : ℝ)*base79 + (57818477802723/10325000000000000000000000000 : ℝ)*base81 + (6806249/625000000000000000000 : ℝ)*base89 + (6806249/625000000000000000000 : ℝ)*base91 + (6806249/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1773_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3609/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2887/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1773_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1773_box_0 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-507895727/5000000000 : ℝ)*x 0 + (1061992503/2000000000 : ℝ)*x 1 + (530996281/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507895727/5000000000 : ℝ)^6 ≤ (6429326272103/100000000000000 : ℝ)^5 := by
    have hnat : (507895727 : ℕ)^6*100000000000000^5 ≤ 6429326272103^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507895727 5000000000 6429326272103 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061992503/2000000000 : ℝ)^6 ≤ (5848166912233/12500000000000 : ℝ)^5 := by
    have hnat : (1061992503 : ℕ)^6*12500000000000^5 ≤ 5848166912233^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061992503 2000000000 5848166912233 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530996281/1000000000 : ℝ)^6 ≤ (46785338416909/100000000000000 : ℝ)^5 := by
    have hnat : (530996281 : ℕ)^6*100000000000000^5 ≤ 46785338416909^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530996281 1000000000 46785338416909 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507895727/5000000000 : ℝ), (1061992503/2000000000 : ℝ), (530996281/1000000000 : ℝ)] ![(6429326272103/100000000000000 : ℝ), (5848166912233/12500000000000 : ℝ), (46785338416909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507895727/5000000000 : ℝ)|^6 ≤ (6429326272103/100000000000000 : ℝ)^5
        have hw : |(-507895727/5000000000 : ℝ)|=(507895727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061992503/2000000000 : ℝ)|^6 ≤ (5848166912233/12500000000000 : ℝ)^5
        have hw : |(1061992503/2000000000 : ℝ)|=(1061992503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530996281/1000000000 : ℝ)|^6 ≤ (46785338416909/100000000000000 : ℝ)^5
        have hw : |(530996281/1000000000 : ℝ)|=(530996281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_1 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2626993691/5000000000 : ℝ)*x 0 + (-1093054151/10000000000 : ℝ)*x 1 + (5309962399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626993691/5000000000 : ℝ)^6 ≤ (46194134076677/100000000000000 : ℝ)^5 := by
    have hnat : (2626993691 : ℕ)^6*100000000000000^5 ≤ 46194134076677^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626993691 5000000000 46194134076677 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093054151/10000000000 : ℝ)^6 ≤ (877566480223/12500000000000 : ℝ)^5 := by
    have hnat : (1093054151 : ℕ)^6*12500000000000^5 ≤ 877566480223^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093054151 10000000000 877566480223 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5309962399/10000000000 : ℝ)^6 ≤ (46785334071393/100000000000000 : ℝ)^5 := by
    have hnat : (5309962399 : ℕ)^6*100000000000000^5 ≤ 46785334071393^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309962399 10000000000 46785334071393 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626993691/5000000000 : ℝ), (-1093054151/10000000000 : ℝ), (5309962399/10000000000 : ℝ)] ![(46194134076677/100000000000000 : ℝ), (877566480223/12500000000000 : ℝ), (46785334071393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626993691/5000000000 : ℝ)|^6 ≤ (46194134076677/100000000000000 : ℝ)^5
        have hw : |(2626993691/5000000000 : ℝ)|=(2626993691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1093054151/10000000000 : ℝ)|^6 ≤ (877566480223/12500000000000 : ℝ)^5
        have hw : |(-1093054151/10000000000 : ℝ)|=(1093054151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5309962399/10000000000 : ℝ)|^6 ≤ (46785334071393/100000000000000 : ℝ)^5
        have hw : |(5309962399/10000000000 : ℝ)|=(5309962399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_2 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5253986491/10000000000 : ℝ)*x 0 + (1327490791/2500000000 : ℝ)*x 1 + (-13663179/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253986491/10000000000 : ℝ)^6 ≤ (46194124676051/100000000000000 : ℝ)^5 := by
    have hnat : (5253986491 : ℕ)^6*100000000000000^5 ≤ 46194124676051^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253986491 10000000000 46194124676051 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1327490791/2500000000 : ℝ)^6 ≤ (23392671079881/50000000000000 : ℝ)^5 := by
    have hnat : (1327490791 : ℕ)^6*50000000000000^5 ≤ 23392671079881^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327490791 2500000000 23392671079881 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13663179/125000000 : ℝ)^6 ≤ (351026657217/5000000000000 : ℝ)^5 := by
    have hnat : (13663179 : ℕ)^6*5000000000000^5 ≤ 351026657217^5*125000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13663179 125000000 351026657217 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253986491/10000000000 : ℝ), (1327490791/2500000000 : ℝ), (-13663179/125000000 : ℝ)] ![(46194124676051/100000000000000 : ℝ), (23392671079881/50000000000000 : ℝ), (351026657217/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253986491/10000000000 : ℝ)|^6 ≤ (46194124676051/100000000000000 : ℝ)^5
        have hw : |(5253986491/10000000000 : ℝ)|=(5253986491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1327490791/2500000000 : ℝ)|^6 ≤ (23392671079881/50000000000000 : ℝ)^5
        have hw : |(1327490791/2500000000 : ℝ)|=(1327490791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13663179/125000000 : ℝ)|^6 ≤ (351026657217/5000000000000 : ℝ)^5
        have hw : |(-13663179/125000000 : ℝ)|=(13663179/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_3 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2068598353/5000000000 : ℝ)*x 0 + (983937377/2500000000 : ℝ)*x 1 + (3935750439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068598353/5000000000 : ℝ)^6 ≤ (34677469967099/100000000000000 : ℝ)^5 := by
    have hnat : (2068598353 : ℕ)^6*100000000000000^5 ≤ 34677469967099^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068598353 5000000000 34677469967099 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983937377/2500000000 : ℝ)^6 ≤ (32661260371711/100000000000000 : ℝ)^5 := by
    have hnat : (983937377 : ℕ)^6*100000000000000^5 ≤ 32661260371711^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983937377 2500000000 32661260371711 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3935750439/10000000000 : ℝ)^6 ≤ (32661269642921/100000000000000 : ℝ)^5 := by
    have hnat : (3935750439 : ℕ)^6*100000000000000^5 ≤ 32661269642921^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3935750439 10000000000 32661269642921 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2068598353/5000000000 : ℝ), (983937377/2500000000 : ℝ), (3935750439/10000000000 : ℝ)] ![(34677469967099/100000000000000 : ℝ), (32661260371711/100000000000000 : ℝ), (32661269642921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2068598353/5000000000 : ℝ)|^6 ≤ (34677469967099/100000000000000 : ℝ)^5
        have hw : |(2068598353/5000000000 : ℝ)|=(2068598353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(983937377/2500000000 : ℝ)|^6 ≤ (32661260371711/100000000000000 : ℝ)^5
        have hw : |(983937377/2500000000 : ℝ)|=(983937377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3935750439/10000000000 : ℝ)|^6 ≤ (32661269642921/100000000000000 : ℝ)^5
        have hw : |(3935750439/10000000000 : ℝ)|=(3935750439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_4 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-300739509/2500000000 : ℝ)*x 0 + (1310366139/2500000000 : ℝ)*x 1 + (2620732739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (300739509/2500000000 : ℝ)^6 ≤ (7875906889909/100000000000000 : ℝ)^5 := by
    have hnat : (300739509 : ℕ)^6*100000000000000^5 ≤ 7875906889909^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300739509 2500000000 7875906889909 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310366139/2500000000 : ℝ)^6 ≤ (2303102084221/5000000000000 : ℝ)^5 := by
    have hnat : (1310366139 : ℕ)^6*5000000000000^5 ≤ 2303102084221^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310366139 2500000000 2303102084221 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620732739/5000000000 : ℝ)^6 ≤ (23031025703737/50000000000000 : ℝ)^5 := by
    have hnat : (2620732739 : ℕ)^6*50000000000000^5 ≤ 23031025703737^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620732739 5000000000 23031025703737 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-300739509/2500000000 : ℝ), (1310366139/2500000000 : ℝ), (2620732739/5000000000 : ℝ)] ![(7875906889909/100000000000000 : ℝ), (2303102084221/5000000000000 : ℝ), (23031025703737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-300739509/2500000000 : ℝ)|^6 ≤ (7875906889909/100000000000000 : ℝ)^5
        have hw : |(-300739509/2500000000 : ℝ)|=(300739509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310366139/2500000000 : ℝ)|^6 ≤ (2303102084221/5000000000000 : ℝ)^5
        have hw : |(1310366139/2500000000 : ℝ)|=(1310366139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620732739/5000000000 : ℝ)|^6 ≤ (23031025703737/50000000000000 : ℝ)^5
        have hw : |(2620732739/5000000000 : ℝ)|=(2620732739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_5 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (211975627/400000000 : ℝ)*x 0 + (-1124599931/10000000000 : ℝ)*x 1 + (5241465697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211975627/400000000 : ℝ)^6 ≤ (9334716232717/20000000000000 : ℝ)^5 := by
    have hnat : (211975627 : ℕ)^6*20000000000000^5 ≤ 9334716232717^5*400000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211975627 400000000 9334716232717 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124599931/10000000000 : ℝ)^6 ≤ (726436509579/10000000000000 : ℝ)^5 := by
    have hnat : (1124599931 : ℕ)^6*10000000000000^5 ≤ 726436509579^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124599931 10000000000 726436509579 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241465697/10000000000 : ℝ)^6 ≤ (46062053716963/100000000000000 : ℝ)^5 := by
    have hnat : (5241465697 : ℕ)^6*100000000000000^5 ≤ 46062053716963^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241465697 10000000000 46062053716963 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211975627/400000000 : ℝ), (-1124599931/10000000000 : ℝ), (5241465697/10000000000 : ℝ)] ![(9334716232717/20000000000000 : ℝ), (726436509579/10000000000000 : ℝ), (46062053716963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211975627/400000000 : ℝ)|^6 ≤ (9334716232717/20000000000000 : ℝ)^5
        have hw : |(211975627/400000000 : ℝ)|=(211975627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1124599931/10000000000 : ℝ)|^6 ≤ (726436509579/10000000000000 : ℝ)^5
        have hw : |(-1124599931/10000000000 : ℝ)|=(1124599931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241465697/10000000000 : ℝ)|^6 ≤ (46062053716963/100000000000000 : ℝ)^5
        have hw : |(5241465697/10000000000 : ℝ)|=(5241465697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_6 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (662423937/1250000000 : ℝ)*x 0 + (327591557/625000000 : ℝ)*x 1 + (-1124599881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662423937/1250000000 : ℝ)^6 ≤ (9334717968117/20000000000000 : ℝ)^5 := by
    have hnat : (662423937 : ℕ)^6*20000000000000^5 ≤ 9334717968117^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662423937 1250000000 9334717968117 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327591557/625000000 : ℝ)^6 ≤ (23031022719329/50000000000000 : ℝ)^5 := by
    have hnat : (327591557 : ℕ)^6*50000000000000^5 ≤ 23031022719329^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327591557 625000000 23031022719329 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124599881/10000000000 : ℝ)^6 ≤ (363218235411/5000000000000 : ℝ)^5 := by
    have hnat : (1124599881 : ℕ)^6*5000000000000^5 ≤ 363218235411^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124599881 10000000000 363218235411 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662423937/1250000000 : ℝ), (327591557/625000000 : ℝ), (-1124599881/10000000000 : ℝ)] ![(9334717968117/20000000000000 : ℝ), (23031022719329/50000000000000 : ℝ), (363218235411/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662423937/1250000000 : ℝ)|^6 ≤ (9334717968117/20000000000000 : ℝ)^5
        have hw : |(662423937/1250000000 : ℝ)|=(662423937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327591557/625000000 : ℝ)|^6 ≤ (23031022719329/50000000000000 : ℝ)^5
        have hw : |(327591557/625000000 : ℝ)|=(327591557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1124599881/10000000000 : ℝ)|^6 ≤ (363218235411/5000000000000 : ℝ)^5
        have hw : |(-1124599881/10000000000 : ℝ)|=(1124599881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_7 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3863093771/10000000000 : ℝ)*x 0 + (2036384871/5000000000 : ℝ)*x 1 + (4072770341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3863093771/10000000000 : ℝ)^6 ≤ (31939072496403/100000000000000 : ℝ)^5 := by
    have hnat : (3863093771 : ℕ)^6*100000000000000^5 ≤ 31939072496403^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3863093771 10000000000 31939072496403 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036384871/5000000000 : ℝ)^6 ≤ (34030460736383/100000000000000 : ℝ)^5 := by
    have hnat : (2036384871 : ℕ)^6*100000000000000^5 ≤ 34030460736383^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036384871 5000000000 34030460736383 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4072770341/10000000000 : ℝ)^6 ≤ (4253808342799/12500000000000 : ℝ)^5 := by
    have hnat : (4072770341 : ℕ)^6*12500000000000^5 ≤ 4253808342799^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072770341 10000000000 4253808342799 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3863093771/10000000000 : ℝ), (2036384871/5000000000 : ℝ), (4072770341/10000000000 : ℝ)] ![(31939072496403/100000000000000 : ℝ), (34030460736383/100000000000000 : ℝ), (4253808342799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3863093771/10000000000 : ℝ)|^6 ≤ (31939072496403/100000000000000 : ℝ)^5
        have hw : |(3863093771/10000000000 : ℝ)|=(3863093771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2036384871/5000000000 : ℝ)|^6 ≤ (34030460736383/100000000000000 : ℝ)^5
        have hw : |(2036384871/5000000000 : ℝ)|=(2036384871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4072770341/10000000000 : ℝ)|^6 ≤ (4253808342799/12500000000000 : ℝ)^5
        have hw : |(4072770341/10000000000 : ℝ)|=(4072770341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_8 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-290800197/2500000000 : ℝ)*x 0 + (5190474267/10000000000 : ℝ)*x 1 + (5321803999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290800197/2500000000 : ℝ)^6 ≤ (472787126461/6250000000000 : ℝ)^5 := by
    have hnat : (290800197 : ℕ)^6*6250000000000^5 ≤ 472787126461^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290800197 2500000000 472787126461 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190474267/10000000000 : ℝ)^6 ≤ (45524842369723/100000000000000 : ℝ)^5 := by
    have hnat : (5190474267 : ℕ)^6*100000000000000^5 ≤ 45524842369723^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190474267 10000000000 45524842369723 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5321803999/10000000000 : ℝ)^6 ≤ (23455281794053/50000000000000 : ℝ)^5 := by
    have hnat : (5321803999 : ℕ)^6*50000000000000^5 ≤ 23455281794053^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5321803999 10000000000 23455281794053 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-290800197/2500000000 : ℝ), (5190474267/10000000000 : ℝ), (5321803999/10000000000 : ℝ)] ![(472787126461/6250000000000 : ℝ), (45524842369723/100000000000000 : ℝ), (23455281794053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-290800197/2500000000 : ℝ)|^6 ≤ (472787126461/6250000000000 : ℝ)^5
        have hw : |(-290800197/2500000000 : ℝ)|=(290800197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190474267/10000000000 : ℝ)|^6 ≤ (45524842369723/100000000000000 : ℝ)^5
        have hw : |(5190474267/10000000000 : ℝ)|=(5190474267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5321803999/10000000000 : ℝ)|^6 ≤ (23455281794053/50000000000000 : ℝ)^5
        have hw : |(5321803999/10000000000 : ℝ)|=(5321803999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_9 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2623071421/5000000000 : ℝ)*x 0 + (-217508001/2000000000 : ℝ)*x 1 + (5321804141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623071421/5000000000 : ℝ)^6 ≤ (23055690737231/50000000000000 : ℝ)^5 := by
    have hnat : (2623071421 : ℕ)^6*50000000000000^5 ≤ 23055690737231^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623071421 5000000000 23055690737231 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217508001/2000000000 : ℝ)^6 ≤ (6978053417101/100000000000000 : ℝ)^5 := by
    have hnat : (217508001 : ℕ)^6*100000000000000^5 ≤ 6978053417101^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217508001 2000000000 6978053417101 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5321804141/10000000000 : ℝ)^6 ≤ (9382113018029/20000000000000 : ℝ)^5 := by
    have hnat : (5321804141 : ℕ)^6*20000000000000^5 ≤ 9382113018029^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5321804141 10000000000 9382113018029 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623071421/5000000000 : ℝ), (-217508001/2000000000 : ℝ), (5321804141/10000000000 : ℝ)] ![(23055690737231/50000000000000 : ℝ), (6978053417101/100000000000000 : ℝ), (9382113018029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623071421/5000000000 : ℝ)|^6 ≤ (23055690737231/50000000000000 : ℝ)^5
        have hw : |(2623071421/5000000000 : ℝ)|=(2623071421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217508001/2000000000 : ℝ)|^6 ≤ (6978053417101/100000000000000 : ℝ)^5
        have hw : |(-217508001/2000000000 : ℝ)|=(217508001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5321804141/10000000000 : ℝ)|^6 ≤ (9382113018029/20000000000000 : ℝ)^5
        have hw : |(5321804141/10000000000 : ℝ)|=(5321804141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_10 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (655767943/1250000000 : ℝ)*x 0 + (2660901973/5000000000 : ℝ)*x 1 + (-67971207/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655767943/1250000000 : ℝ)^6 ≤ (46111388878803/100000000000000 : ℝ)^5 := by
    have hnat : (655767943 : ℕ)^6*100000000000000^5 ≤ 46111388878803^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655767943 1250000000 46111388878803 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2660901973/5000000000 : ℝ)^6 ≤ (9382112605497/20000000000000 : ℝ)^5 := by
    have hnat : (2660901973 : ℕ)^6*20000000000000^5 ≤ 9382112605497^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2660901973 5000000000 9382112605497 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67971207/625000000 : ℝ)^6 ≤ (1744512020313/25000000000000 : ℝ)^5 := by
    have hnat : (67971207 : ℕ)^6*25000000000000^5 ≤ 1744512020313^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67971207 625000000 1744512020313 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655767943/1250000000 : ℝ), (2660901973/5000000000 : ℝ), (-67971207/625000000 : ℝ)] ![(46111388878803/100000000000000 : ℝ), (9382112605497/20000000000000 : ℝ), (1744512020313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655767943/1250000000 : ℝ)|^6 ≤ (46111388878803/100000000000000 : ℝ)^5
        have hw : |(655767943/1250000000 : ℝ)|=(655767943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2660901973/5000000000 : ℝ)|^6 ≤ (9382112605497/20000000000000 : ℝ)^5
        have hw : |(2660901973/5000000000 : ℝ)|=(2660901973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67971207/625000000 : ℝ)|^6 ≤ (1744512020313/25000000000000 : ℝ)^5
        have hw : |(-67971207/625000000 : ℝ)|=(67971207/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_11 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4184062839/10000000000 : ℝ)*x 0 + (978010123/2500000000 : ℝ)*x 1 + (61125641/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184062839/10000000000 : ℝ)^6 ≤ (3514939369501/10000000000000 : ℝ)^5 := by
    have hnat : (4184062839 : ℕ)^6*10000000000000^5 ≤ 3514939369501^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184062839 10000000000 3514939369501 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978010123/2500000000 : ℝ)^6 ≤ (16212650251571/50000000000000 : ℝ)^5 := by
    have hnat : (978010123 : ℕ)^6*50000000000000^5 ≤ 16212650251571^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978010123 2500000000 16212650251571 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61125641/156250000 : ℝ)^6 ≤ (16212652897289/50000000000000 : ℝ)^5 := by
    have hnat : (61125641 : ℕ)^6*50000000000000^5 ≤ 16212652897289^5*156250000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61125641 156250000 16212652897289 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184062839/10000000000 : ℝ), (978010123/2500000000 : ℝ), (61125641/156250000 : ℝ)] ![(3514939369501/10000000000000 : ℝ), (16212650251571/50000000000000 : ℝ), (16212652897289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184062839/10000000000 : ℝ)|^6 ≤ (3514939369501/10000000000000 : ℝ)^5
        have hw : |(4184062839/10000000000 : ℝ)|=(4184062839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(978010123/2500000000 : ℝ)|^6 ≤ (16212650251571/50000000000000 : ℝ)^5
        have hw : |(978010123/2500000000 : ℝ)|=(978010123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(61125641/156250000 : ℝ)|^6 ≤ (16212652897289/50000000000000 : ℝ)^5
        have hw : |(61125641/156250000 : ℝ)|=(61125641/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_12 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-527322359/5000000000 : ℝ)*x 0 + (268011919/500000000 : ℝ)*x 1 + (1046301347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527322359/5000000000 : ℝ)^6 ≤ (6725544000081/100000000000000 : ℝ)^5 := by
    have hnat : (527322359 : ℕ)^6*100000000000000^5 ≤ 6725544000081^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527322359 5000000000 6725544000081 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268011919/500000000 : ℝ)^6 ≤ (47317405650587/100000000000000 : ℝ)^5 := by
    have hnat : (268011919 : ℕ)^6*100000000000000^5 ≤ 47317405650587^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268011919 500000000 47317405650587 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046301347/2000000000 : ℝ)^6 ≤ (22978525165487/50000000000000 : ℝ)^5 := by
    have hnat : (1046301347 : ℕ)^6*50000000000000^5 ≤ 22978525165487^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046301347 2000000000 22978525165487 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527322359/5000000000 : ℝ), (268011919/500000000 : ℝ), (1046301347/2000000000 : ℝ)] ![(6725544000081/100000000000000 : ℝ), (47317405650587/100000000000000 : ℝ), (22978525165487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527322359/5000000000 : ℝ)|^6 ≤ (6725544000081/100000000000000 : ℝ)^5
        have hw : |(-527322359/5000000000 : ℝ)|=(527322359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268011919/500000000 : ℝ)|^6 ≤ (47317405650587/100000000000000 : ℝ)^5
        have hw : |(268011919/500000000 : ℝ)|=(268011919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046301347/2000000000 : ℝ)|^6 ≤ (22978525165487/50000000000000 : ℝ)^5
        have hw : |(1046301347/2000000000 : ℝ)|=(1046301347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_13 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5305997001/10000000000 : ℝ)*x 0 + (-1129134789/10000000000 : ℝ)*x 1 + (2615753743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305997001/10000000000 : ℝ)^6 ≤ (46743410924163/100000000000000 : ℝ)^5 := by
    have hnat : (5305997001 : ℕ)^6*100000000000000^5 ≤ 46743410924163^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305997001 10000000000 46743410924163 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129134789/10000000000 : ℝ)^6 ≤ (1824882702689/25000000000000 : ℝ)^5 := by
    have hnat : (1129134789 : ℕ)^6*25000000000000^5 ≤ 1824882702689^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129134789 10000000000 1824882702689 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615753743/5000000000 : ℝ)^6 ≤ (45957058247717/100000000000000 : ℝ)^5 := by
    have hnat : (2615753743 : ℕ)^6*100000000000000^5 ≤ 45957058247717^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615753743 5000000000 45957058247717 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305997001/10000000000 : ℝ), (-1129134789/10000000000 : ℝ), (2615753743/5000000000 : ℝ)] ![(46743410924163/100000000000000 : ℝ), (1824882702689/25000000000000 : ℝ), (45957058247717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305997001/10000000000 : ℝ)|^6 ≤ (46743410924163/100000000000000 : ℝ)^5
        have hw : |(5305997001/10000000000 : ℝ)|=(5305997001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129134789/10000000000 : ℝ)|^6 ≤ (1824882702689/25000000000000 : ℝ)^5
        have hw : |(-1129134789/10000000000 : ℝ)|=(1129134789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615753743/5000000000 : ℝ)|^6 ≤ (45957058247717/100000000000000 : ℝ)^5
        have hw : |(2615753743/5000000000 : ℝ)|=(2615753743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_14 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (1326499501/2500000000 : ℝ)*x 0 + (1046301213/2000000000 : ℝ)*x 1 + (-1129135353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326499501/2500000000 : ℝ)^6 ≤ (4674342152733/10000000000000 : ℝ)^5 := by
    have hnat : (1326499501 : ℕ)^6*10000000000000^5 ≤ 4674342152733^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326499501 2500000000 4674342152733 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046301213/2000000000 : ℝ)^6 ≤ (459570432681/1000000000000 : ℝ)^5 := by
    have hnat : (1046301213 : ℕ)^6*1000000000000^5 ≤ 459570432681^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046301213 2000000000 459570432681 1000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129135353/10000000000 : ℝ)^6 ≤ (7299535186073/100000000000000 : ℝ)^5 := by
    have hnat : (1129135353 : ℕ)^6*100000000000000^5 ≤ 7299535186073^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129135353 10000000000 7299535186073 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326499501/2500000000 : ℝ), (1046301213/2000000000 : ℝ), (-1129135353/10000000000 : ℝ)] ![(4674342152733/10000000000000 : ℝ), (459570432681/1000000000000 : ℝ), (7299535186073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326499501/2500000000 : ℝ)|^6 ≤ (4674342152733/10000000000000 : ℝ)^5
        have hw : |(1326499501/2500000000 : ℝ)|=(1326499501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046301213/2000000000 : ℝ)|^6 ≤ (459570432681/1000000000000 : ℝ)^5
        have hw : |(1046301213/2000000000 : ℝ)|=(1046301213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129135353/10000000000 : ℝ)|^6 ≤ (7299535186073/100000000000000 : ℝ)^5
        have hw : |(-1129135353/10000000000 : ℝ)|=(1129135353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1773_box_15 (p : ℝ) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (764561407/2000000000 : ℝ)*x 0 + (4092670703/10000000000 : ℝ)*x 1 + (2046335689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (764561407/2000000000 : ℝ)^6 ≤ (15769896979329/50000000000000 : ℝ)^5 := by
    have hnat : (764561407 : ℕ)^6*50000000000000^5 ≤ 15769896979329^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764561407 2000000000 15769896979329 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4092670703/10000000000 : ℝ)^6 ≤ (8557524906981/25000000000000 : ℝ)^5 := by
    have hnat : (4092670703 : ℕ)^6*25000000000000^5 ≤ 8557524906981^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4092670703 10000000000 8557524906981 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2046335689/5000000000 : ℝ)^6 ≤ (34230106402567/100000000000000 : ℝ)^5 := by
    have hnat : (2046335689 : ℕ)^6*100000000000000^5 ≤ 34230106402567^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046335689 5000000000 34230106402567 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(764561407/2000000000 : ℝ), (4092670703/10000000000 : ℝ), (2046335689/5000000000 : ℝ)] ![(15769896979329/50000000000000 : ℝ), (8557524906981/25000000000000 : ℝ), (34230106402567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(764561407/2000000000 : ℝ)|^6 ≤ (15769896979329/50000000000000 : ℝ)^5
        have hw : |(764561407/2000000000 : ℝ)|=(764561407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4092670703/10000000000 : ℝ)|^6 ≤ (8557524906981/25000000000000 : ℝ)^5
        have hw : |(4092670703/10000000000 : ℝ)|=(4092670703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2046335689/5000000000 : ℝ)|^6 ≤ (34230106402567/100000000000000 : ℝ)^5
        have hw : |(2046335689/5000000000 : ℝ)|=(2046335689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1773_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2887/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16417/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(12627/20000 : ℝ) ∧ (2709/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (89313/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2887/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (12371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2887/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (12371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2887/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (12371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2887/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (12371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2887/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (12371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2887/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (12371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (12371/100000 : ℝ) ^ (6143/1024 : ℝ) ≤ (359182496610181/100000000000000000000 : ℝ) := by
    have hpowers : (12371/100000 : ℝ)^6143 ≤ (359182496610181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12371 : ℕ)^6143*100000000000000000000^1024 ≤ 359182496610181^1024*100000^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12371 100000 359182496610181 100000000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12371/100000 : ℝ)) (X := (359182496610181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2887/20000 : ℝ) ^ (6143/1024 : ℝ) ≤ (906403578251443/100000000000000000000 : ℝ) := by
    have hpowers : (2887/20000 : ℝ)^6143 ≤ (906403578251443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2887 : ℕ)^6143*100000000000000000000^1024 ≤ 906403578251443^1024*20000^6143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2887 20000 906403578251443 100000000000000000000 6143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2887/20000 : ℝ)) (X := (906403578251443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000359182496610181/50000000000000000000 : ℝ) ≤ (10000011974663053/10000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (50000359182496610181/50000000000000000000 : ℝ)^1024 ≤ (10000011974663053/10000000000000000 : ℝ)^6143 := by
      have hnat : (50000359182496610181 : ℕ)^1024*10000000000000000^6143 ≤ 10000011974663053^6143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000359182496610181 50000000000000000000 10000011974663053 10000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000011974663053/10000000000000000 : ℝ)) (X := (50000359182496610181/50000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12500158198259357703/12500000000000000000 : ℝ) ≤ (5000010548211843/5000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (12500158198259357703/12500000000000000000 : ℝ)^1024 ≤ (5000010548211843/5000000000000000 : ℝ)^6143 := by
      have hnat : (12500158198259357703 : ℕ)^1024*5000000000000000^6143 ≤ 5000010548211843^6143*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500158198259357703 12500000000000000000 5000010548211843 5000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000010548211843/5000000000000000 : ℝ)) (X := (12500158198259357703/12500000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50000906403578251443/50000000000000000000 : ℝ) ≤ (10000030218184319/10000000000000000 : ℝ) ^ (6143/1024 : ℝ) := by
    have hpowers : (50000906403578251443/50000000000000000000 : ℝ)^1024 ≤ (10000030218184319/10000000000000000 : ℝ)^6143 := by
      have hnat : (50000906403578251443 : ℕ)^1024*10000000000000000^6143 ≤ 10000030218184319^6143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000906403578251443 50000000000000000000 10000030218184319 10000000000000000 1024 6143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030218184319/10000000000000000 : ℝ)) (X := (50000906403578251443/50000000000000000000 : ℝ)) (by norm_num) 6143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(359182496610181/100000000000000000000 : ℝ) ≤ ((10319899512551479853/10320000000000000000 : ℝ)+2*(9121760633/206400000000000 : ℝ)*(12371/100000 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (10319899512551479853/10320000000000000000 : ℝ)+2*(9121760633/206400000000000 : ℝ)*(12371/100000 : ℝ)=(10000011974663053/10000000000000000 : ℝ) by norm_num, show 1+2*(359182496610181/100000000000000000000 : ℝ)=(50000359182496610181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(906403578251443/100000000000000000000 : ℝ)+(359182496610181/100000000000000000000 : ℝ) ≤ ((10319899512551479853/10320000000000000000 : ℝ)+(9121760633/206400000000000 : ℝ)*((2887/20000 : ℝ)+(12371/100000 : ℝ)))^(6143/1024 : ℝ) := by
    rw [show (10319899512551479853/10320000000000000000 : ℝ)+(9121760633/206400000000000 : ℝ)*((2887/20000 : ℝ)+(12371/100000 : ℝ))=(5000010548211843/5000000000000000 : ℝ) by norm_num, show 1+(906403578251443/100000000000000000000 : ℝ)+(359182496610181/100000000000000000000 : ℝ)=(12500158198259357703/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(906403578251443/100000000000000000000 : ℝ) ≤ ((10319899512551479853/10320000000000000000 : ℝ)+2*(9121760633/206400000000000 : ℝ)*(2887/20000 : ℝ))^(6143/1024 : ℝ) := by
    rw [show (10319899512551479853/10320000000000000000 : ℝ)+2*(9121760633/206400000000000 : ℝ)*(2887/20000 : ℝ)=(10000030218184319/10000000000000000 : ℝ) by norm_num, show 1+2*(906403578251443/100000000000000000000 : ℝ)=(50000906403578251443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10319899512551479853/10320000000000000000 : ℝ)*(X 1 0+X 2 0)+(9121760633/206400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12371/100000 : ℝ)) (hi := (2887/20000 : ℝ)) (c := (10319899512551479853/10320000000000000000 : ℝ)) (alpha := (9121760633/206400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10319899512551479853/10320000000000000000 : ℝ)*(X 0 1+X 2 1)+(9121760633/206400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12371/100000 : ℝ)) (hi := (2887/20000 : ℝ)) (c := (10319899512551479853/10320000000000000000 : ℝ)) (alpha := (9121760633/206400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10319899512551479853/10320000000000000000 : ℝ)*(X 0 2+X 1 2)+(9121760633/206400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6143/1024 : ℝ)) (lo := (12371/100000 : ℝ)) (hi := (2887/20000 : ℝ)) (c := (10319899512551479853/10320000000000000000 : ℝ)) (alpha := (9121760633/206400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-507895727/5000000000 : ℝ)*X 0 0+(1061992503/2000000000 : ℝ)*X 0 1+(530996281/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2626993691/5000000000 : ℝ)*X 1 0+(-1093054151/10000000000 : ℝ)*X 1 1+(5309962399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5253986491/10000000000 : ℝ)*X 2 0+(1327490791/2500000000 : ℝ)*X 2 1+(-13663179/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2068598353/5000000000 : ℝ)*X 0 0+(983937377/2500000000 : ℝ)*X 0 1+(3935750439/10000000000 : ℝ)*X 0 2+(2068598353/5000000000 : ℝ)*X 1 0+(983937377/2500000000 : ℝ)*X 1 1+(3935750439/10000000000 : ℝ)*X 1 2+(2068598353/5000000000 : ℝ)*X 2 0+(983937377/2500000000 : ℝ)*X 2 1+(3935750439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-300739509/2500000000 : ℝ)*X 0 0+(1310366139/2500000000 : ℝ)*X 0 1+(2620732739/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211975627/400000000 : ℝ)*X 1 0+(-1124599931/10000000000 : ℝ)*X 1 1+(5241465697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662423937/1250000000 : ℝ)*X 2 0+(327591557/625000000 : ℝ)*X 2 1+(-1124599881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3863093771/10000000000 : ℝ)*X 0 0+(2036384871/5000000000 : ℝ)*X 0 1+(4072770341/10000000000 : ℝ)*X 0 2+(3863093771/10000000000 : ℝ)*X 1 0+(2036384871/5000000000 : ℝ)*X 1 1+(4072770341/10000000000 : ℝ)*X 1 2+(3863093771/10000000000 : ℝ)*X 2 0+(2036384871/5000000000 : ℝ)*X 2 1+(4072770341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-290800197/2500000000 : ℝ)*X 0 0+(5190474267/10000000000 : ℝ)*X 0 1+(5321803999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2623071421/5000000000 : ℝ)*X 1 0+(-217508001/2000000000 : ℝ)*X 1 1+(5321804141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((655767943/1250000000 : ℝ)*X 2 0+(2660901973/5000000000 : ℝ)*X 2 1+(-67971207/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4184062839/10000000000 : ℝ)*X 0 0+(978010123/2500000000 : ℝ)*X 0 1+(61125641/156250000 : ℝ)*X 0 2+(4184062839/10000000000 : ℝ)*X 1 0+(978010123/2500000000 : ℝ)*X 1 1+(61125641/156250000 : ℝ)*X 1 2+(4184062839/10000000000 : ℝ)*X 2 0+(978010123/2500000000 : ℝ)*X 2 1+(61125641/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-527322359/5000000000 : ℝ)*X 0 0+(268011919/500000000 : ℝ)*X 0 1+(1046301347/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5305997001/10000000000 : ℝ)*X 1 0+(-1129134789/10000000000 : ℝ)*X 1 1+(2615753743/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1326499501/2500000000 : ℝ)*X 2 0+(1046301213/2000000000 : ℝ)*X 2 1+(-1129135353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((764561407/2000000000 : ℝ)*X 0 0+(4092670703/10000000000 : ℝ)*X 0 1+(2046335689/5000000000 : ℝ)*X 0 2+(764561407/2000000000 : ℝ)*X 1 0+(4092670703/10000000000 : ℝ)*X 1 1+(2046335689/5000000000 : ℝ)*X 1 2+(764561407/2000000000 : ℝ)*X 2 0+(4092670703/10000000000 : ℝ)*X 2 1+(2046335689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1773_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16417/25000 : ℝ) ≤ (-28236171581315890922638710330731/43000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7793971/4000000000000 : ℝ)*(lower2) + (222129657/100000000000000 : ℝ)*(lower3) + (54229199/25000000000000 : ℝ)*(upper5) + (1167859034580073/25000000000000 : ℝ)*(major0) + (1167859034580073/25000000000000 : ℝ)*(major1) + (1167859034580073/25000000000000 : ℝ)*(major2) + (30709811047/100000000000000 : ℝ)*(sp2) + (68725917/1250000000000 : ℝ)*(sp3) + (1834402584833603/25000000000000 : ℝ)*(sp4) + (7337225907901149/100000000000000 : ℝ)*(sp5) + (3668800535126067/50000000000000 : ℝ)*(sp6) + (506780875901457/25000000000000 : ℝ)*(sp7) + (335011387/1562500000000 : ℝ)*(sp12) + (405872162033/100000000000000 : ℝ)*(sp13) + (2027129001679189/100000000000000 : ℝ)*(f.failure) + (7337631780063181/100000000000000 : ℝ)*(f.sum) + (22912159947151/2580000000000000000000000000 : ℝ)*base66 + (328695427819593577/86000000000000000000000000000000 : ℝ)*base68 + (1036481159484406423/86000000000000000000000000000000 : ℝ)*base69 + (826611174787593577/86000000000000000000000000000000 : ℝ)*base72 + (1342867703791/2580000000000000000000000000 : ℝ)*base74 + (623248619365593577/86000000000000000000000000000000 : ℝ)*base76 + (420654189025593577/86000000000000000000000000000000 : ℝ)*base78 + (549228863836406423/86000000000000000000000000000000 : ℝ)*base79 + (8594758767689/2580000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (58996447/10000000000000000000000 : ℝ)*base89 + (58996447/10000000000000000000000 : ℝ)*base91 + (58996447/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (12627/20000 : ℝ) ≤ (27149280923977716864043562585019/43000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18722867/50000000000000 : ℝ)*(lower0) + (81511693/25000000000000 : ℝ)*(upper2) + (80896493/50000000000000 : ℝ)*(lower4) + (20907767/100000000000000 : ℝ)*(lower5) + (2402973472247823/50000000000000 : ℝ)*(major0) + (2402973472247823/50000000000000 : ℝ)*(major1) + (2402973472247823/50000000000000 : ℝ)*(major2) + (1876327455869373/25000000000000 : ℝ)*(sp0) + (375267457049997/5000000000000 : ℝ)*(sp1) + (3752654651236511/50000000000000 : ℝ)*(sp2) + (2085493677412981/100000000000000 : ℝ)*(sp3) + (19919263459/50000000000000 : ℝ)*(sp6) + (5116373727/100000000000000 : ℝ)*(sp7) + (39317522447/100000000000000 : ℝ)*(sp12) + (521374698446677/25000000000000 : ℝ)*(f.failure) + (375267457049997/5000000000000 : ℝ)*(f.sum) + (13466029226427/1720000000000000000000000000 : ℝ)*base66 + (1810671533751186673/172000000000000000000000000000000 : ℝ)*base67 + (1852373354996813327/172000000000000000000000000000000 : ℝ)*base70 + (1947991517940813327/172000000000000000000000000000000 : ℝ)*base72 + (7004509402413/1720000000000000000000000000 : ℝ)*base73 + (1555673870136813327/172000000000000000000000000000000 : ℝ)*base76 + (3543029742540813327/172000000000000000000000000000000 : ℝ)*base78 + (1801523614696813327/172000000000000000000000000000000 : ℝ)*base80 + (2689980689693/1720000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2452129/2500000000000000000000 : ℝ)*base90 + (2452129/2500000000000000000000 : ℝ)*base92 + (2452129/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2709/3125 : ℝ) ≤ (37276899011796308744631990965349/43000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226575601/100000000000000 : ℝ)*(lower1) + (184181509/50000000000000 : ℝ)*(lower3) + (599068641/100000000000000 : ℝ)*(upper4) + (2440316690911567/50000000000000 : ℝ)*(major0) + (2440316690911567/50000000000000 : ℝ)*(major1) + (2440316690911567/50000000000000 : ℝ)*(major2) + (2020296757/20000000000000 : ℝ)*(sp0) + (110572468961/50000000000000 : ℝ)*(sp1) + (151735990329/50000000000000 : ℝ)*(sp2) + (15534413213/10000000000000 : ℝ)*(sp3) + (76144515188341/1000000000000 : ℝ)*(sp8) + (1903560118844991/25000000000000 : ℝ)*(sp9) + (1903539537084307/25000000000000 : ℝ)*(sp10) + (66179780570527/3125000000000 : ℝ)*(sp11) + (1058954161194497/50000000000000 : ℝ)*(f.failure) + (3807230810158943/50000000000000 : ℝ)*(f.sum) + (15626363074151/5160000000000000000000000000 : ℝ)*base65 + (2836176302450903217/172000000000000000000000000000000 : ℝ)*base67 + (735791000534903217/172000000000000000000000000000000 : ℝ)*base69 + (1374562470903217/172000000000000000000000000000000 : ℝ)*base71 + (8740040698151/5160000000000000000000000000 : ℝ)*base73 + (56651536409096783/172000000000000000000000000000000 : ℝ)*base76 + (616751136974903217/172000000000000000000000000000000 : ℝ)*base77 + (1582784846950903217/172000000000000000000000000000000 : ℝ)*base79 + (27016301334311/5160000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (56314269/5000000000000000000000 : ℝ)*base90 + (56314269/5000000000000000000000 : ℝ)*base92 + (56314269/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-89313/100000 : ℝ) ≤ (-153614580341170366431416575310199/172000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (296673841/100000000000000 : ℝ)*(lower0) + (241330567/50000000000000 : ℝ)*(lower1) + (40436129/50000000000000 : ℝ)*(lower2) + (4941299873499117/100000000000000 : ℝ)*(major0) + (4941299873499117/100000000000000 : ℝ)*(major1) + (4941299873499117/100000000000000 : ℝ)*(major2) + (6768288489/100000000000000 : ℝ)*(sp4) + (1056945337123/100000000000000 : ℝ)*(sp6) + (3041916139/10000000000000 : ℝ)*(sp7) + (1301057077/12500000000000 : ℝ)*(sp8) + (3884059410002263/50000000000000 : ℝ)*(sp12) + (7768135996749631/100000000000000 : ℝ)*(sp13) + (7767079051412507/100000000000000 : ℝ)*(sp14) + (1072101799297591/50000000000000 : ℝ)*(sp15) + (536058504439143/25000000000000 : ℝ)*(f.failure) + (7768135996749631/100000000000000 : ℝ)*(f.sum) + (17475716766487/3440000000000000000000000000 : ℝ)*base65 + (2081480099097386733/344000000000000000000000000000000 : ℝ)*base68 + (875102701337386733/344000000000000000000000000000000 : ℝ)*base70 + (2655906823473386733/344000000000000000000000000000000 : ℝ)*base72 + (20515131907207/3440000000000000000000000000 : ℝ)*base73 + (1512372562742613267/344000000000000000000000000000000 : ℝ)*base75 + (649728202793386733/344000000000000000000000000000000 : ℝ)*base78 + (3782419961022613267/344000000000000000000000000000000 : ℝ)*base79 + (16580834918807/3440000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (19036011/2500000000000000000000 : ℝ)*base90 + (19036011/2500000000000000000000 : ℝ)*base92 + (19036011/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1773_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2887/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16417/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(12627/20000 : ℝ) else (2709/3125 : ℝ) ≤ X j i ∧ X j i ≤ (89313/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1773_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1773_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3609/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16417/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(12627/20000 : ℝ) else (2709/3125 : ℝ) ≤ X j i ∧ X j i ≤ (89313/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1773_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1773_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6143/1024 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (230445923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3609/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (12371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16417/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(12627/20000 : ℝ) else (2709/3125 : ℝ) ≤ X j i ∧ X j i ≤ (89313/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1773_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
