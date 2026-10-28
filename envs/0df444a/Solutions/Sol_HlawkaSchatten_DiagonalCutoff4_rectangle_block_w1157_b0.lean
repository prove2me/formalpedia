-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1157_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:38:01.184717+00:00
-- url     : https://prove2.me/submissions/8432ed37-d735-481a-9ce1-7f5bb2b29731

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
theorem support_rectangle_w1157_s0_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1887072367/10000000000 : ℝ)*x 0 + (3025434877/5000000000 : ℝ)*x 1 + (239118323/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1887072367/10000000000 : ℝ)^4175 ≤ (2195164490917/20000000000000 : ℝ)^3151 := by
    have hnat : (1887072367 : ℕ)^4175*20000000000000^3151 ≤ 2195164490917^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887072367 10000000000 2195164490917 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3025434877/5000000000 : ℝ)^4175 ≤ (51394161450731/100000000000000 : ℝ)^3151 := by
    have hnat : (3025434877 : ℕ)^4175*100000000000000^3151 ≤ 51394161450731^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3025434877 5000000000 51394161450731 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239118323/500000000 : ℝ)^4175 ≤ (37630016077807/100000000000000 : ℝ)^3151 := by
    have hnat : (239118323 : ℕ)^4175*100000000000000^3151 ≤ 37630016077807^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239118323 500000000 37630016077807 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1887072367/10000000000 : ℝ), (3025434877/5000000000 : ℝ), (239118323/500000000 : ℝ)] ![(2195164490917/20000000000000 : ℝ), (51394161450731/100000000000000 : ℝ), (37630016077807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1887072367/10000000000 : ℝ)|^4175 ≤ (2195164490917/20000000000000 : ℝ)^3151
        have hw : |(-1887072367/10000000000 : ℝ)|=(1887072367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3025434877/5000000000 : ℝ)|^4175 ≤ (51394161450731/100000000000000 : ℝ)^3151
        have hw : |(3025434877/5000000000 : ℝ)|=(3025434877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(239118323/500000000 : ℝ)|^4175 ≤ (37630016077807/100000000000000 : ℝ)^3151
        have hw : |(239118323/500000000 : ℝ)|=(239118323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s0_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (44127589/80000000 : ℝ)*x 0 + (-52292379/200000000 : ℝ)*x 1 + (1195591623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44127589/80000000 : ℝ)^4175 ≤ (2273122998019/5000000000000 : ℝ)^3151 := by
    have hnat : (44127589 : ℕ)^4175*5000000000000^3151 ≤ 2273122998019^3151*80000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44127589 80000000 2273122998019 5000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52292379/200000000 : ℝ)^4175 ≤ (8453761809433/50000000000000 : ℝ)^3151 := by
    have hnat : (52292379 : ℕ)^4175*50000000000000^3151 ≤ 8453761809433^3151*200000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52292379 200000000 8453761809433 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195591623/2500000000 : ℝ)^4175 ≤ (1505200656457/4000000000000 : ℝ)^3151 := by
    have hnat : (1195591623 : ℕ)^4175*4000000000000^3151 ≤ 1505200656457^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195591623 2500000000 1505200656457 4000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44127589/80000000 : ℝ), (-52292379/200000000 : ℝ), (1195591623/2500000000 : ℝ)] ![(2273122998019/5000000000000 : ℝ), (8453761809433/50000000000000 : ℝ), (1505200656457/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44127589/80000000 : ℝ)|^4175 ≤ (2273122998019/5000000000000 : ℝ)^3151
        have hw : |(44127589/80000000 : ℝ)|=(44127589/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52292379/200000000 : ℝ)|^4175 ≤ (8453761809433/50000000000000 : ℝ)^3151
        have hw : |(-52292379/200000000 : ℝ)|=(52292379/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195591623/2500000000 : ℝ)|^4175 ≤ (1505200656457/4000000000000 : ℝ)^3151
        have hw : |(1195591623/2500000000 : ℝ)|=(1195591623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s0_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1103189721/2000000000 : ℝ)*x 0 + (1195591627/2500000000 : ℝ)*x 1 + (-522923791/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103189721/2000000000 : ℝ)^4175 ≤ (45462459741971/100000000000000 : ℝ)^3151 := by
    have hnat : (1103189721 : ℕ)^4175*100000000000000^3151 ≤ 45462459741971^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103189721 2000000000 45462459741971 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195591627/2500000000 : ℝ)^4175 ≤ (18815008289117/50000000000000 : ℝ)^3151 := by
    have hnat : (1195591627 : ℕ)^4175*50000000000000^3151 ≤ 18815008289117^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195591627 2500000000 18815008289117 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522923791/2000000000 : ℝ)^4175 ≤ (8453761830853/50000000000000 : ℝ)^3151 := by
    have hnat : (522923791 : ℕ)^4175*50000000000000^3151 ≤ 8453761830853^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522923791 2000000000 8453761830853 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103189721/2000000000 : ℝ), (1195591627/2500000000 : ℝ), (-522923791/2000000000 : ℝ)] ![(45462459741971/100000000000000 : ℝ), (18815008289117/50000000000000 : ℝ), (8453761830853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103189721/2000000000 : ℝ)|^4175 ≤ (45462459741971/100000000000000 : ℝ)^3151
        have hw : |(1103189721/2000000000 : ℝ)|=(1103189721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195591627/2500000000 : ℝ)|^4175 ≤ (18815008289117/50000000000000 : ℝ)^3151
        have hw : |(1195591627/2500000000 : ℝ)|=(1195591627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522923791/2000000000 : ℝ)|^4175 ≤ (8453761830853/50000000000000 : ℝ)^3151
        have hw : |(-522923791/2000000000 : ℝ)|=(522923791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s0_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2099890209/5000000000 : ℝ)*x 0 + (3120393759/10000000000 : ℝ)*x 1 + (5651475401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099890209/5000000000 : ℝ)^4175 ≤ (15839964226893/50000000000000 : ℝ)^3151 := by
    have hnat : (2099890209 : ℕ)^4175*50000000000000^3151 ≤ 15839964226893^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099890209 5000000000 15839964226893 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120393759/10000000000 : ℝ)^4175 ≤ (4274344186513/20000000000000 : ℝ)^3151 := by
    have hnat : (3120393759 : ℕ)^4175*20000000000000^3151 ≤ 4274344186513^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120393759 10000000000 4274344186513 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5651475401/10000000000 : ℝ)^4175 ≤ (46948350601981/100000000000000 : ℝ)^3151 := by
    have hnat : (5651475401 : ℕ)^4175*100000000000000^3151 ≤ 46948350601981^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5651475401 10000000000 46948350601981 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099890209/5000000000 : ℝ), (3120393759/10000000000 : ℝ), (5651475401/10000000000 : ℝ)] ![(15839964226893/50000000000000 : ℝ), (4274344186513/20000000000000 : ℝ), (46948350601981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099890209/5000000000 : ℝ)|^4175 ≤ (15839964226893/50000000000000 : ℝ)^3151
        have hw : |(2099890209/5000000000 : ℝ)|=(2099890209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120393759/10000000000 : ℝ)|^4175 ≤ (4274344186513/20000000000000 : ℝ)^3151
        have hw : |(3120393759/10000000000 : ℝ)|=(3120393759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5651475401/10000000000 : ℝ)|^4175 ≤ (46948350601981/100000000000000 : ℝ)^3151
        have hw : |(5651475401/10000000000 : ℝ)|=(5651475401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s0_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-946086969/5000000000 : ℝ)*x 0 + (4815082671/10000000000 : ℝ)*x 1 + (3008501093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946086969/5000000000 : ℝ)^4175 ≤ (1376894364747/12500000000000 : ℝ)^3151 := by
    have hnat : (946086969 : ℕ)^4175*12500000000000^3151 ≤ 1376894364747^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946086969 5000000000 1376894364747 12500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815082671/10000000000 : ℝ)^4175 ≤ (1518859185863/4000000000000 : ℝ)^3151 := by
    have hnat : (4815082671 : ℕ)^4175*4000000000000^3151 ≤ 1518859185863^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815082671 10000000000 1518859185863 4000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3008501093/5000000000 : ℝ)^4175 ≤ (12753341355223/25000000000000 : ℝ)^3151 := by
    have hnat : (3008501093 : ℕ)^4175*25000000000000^3151 ≤ 12753341355223^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008501093 5000000000 12753341355223 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-946086969/5000000000 : ℝ), (4815082671/10000000000 : ℝ), (3008501093/5000000000 : ℝ)] ![(1376894364747/12500000000000 : ℝ), (1518859185863/4000000000000 : ℝ), (12753341355223/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-946086969/5000000000 : ℝ)|^4175 ≤ (1376894364747/12500000000000 : ℝ)^3151
        have hw : |(-946086969/5000000000 : ℝ)|=(946086969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815082671/10000000000 : ℝ)|^4175 ≤ (1518859185863/4000000000000 : ℝ)^3151
        have hw : |(4815082671/10000000000 : ℝ)|=(4815082671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3008501093/5000000000 : ℝ)|^4175 ≤ (12753341355223/25000000000000 : ℝ)^3151
        have hw : |(3008501093/5000000000 : ℝ)|=(3008501093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s0_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2585597521/5000000000 : ℝ)*x 0 + (-1379983417/10000000000 : ℝ)*x 1 + (3008500999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585597521/5000000000 : ℝ)^4175 ≤ (41736380582033/100000000000000 : ℝ)^3151 := by
    have hnat : (2585597521 : ℕ)^4175*100000000000000^3151 ≤ 41736380582033^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585597521 5000000000 41736380582033 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379983417/10000000000 : ℝ)^4175 ≤ (1812564024513/25000000000000 : ℝ)^3151 := by
    have hnat : (1379983417 : ℕ)^4175*25000000000000^3151 ≤ 1812564024513^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379983417 10000000000 1812564024513 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3008500999/5000000000 : ℝ)^4175 ≤ (5101336330901/10000000000000 : ℝ)^3151 := by
    have hnat : (3008500999 : ℕ)^4175*10000000000000^3151 ≤ 5101336330901^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008500999 5000000000 5101336330901 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585597521/5000000000 : ℝ), (-1379983417/10000000000 : ℝ), (3008500999/5000000000 : ℝ)] ![(41736380582033/100000000000000 : ℝ), (1812564024513/25000000000000 : ℝ), (5101336330901/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585597521/5000000000 : ℝ)|^4175 ≤ (41736380582033/100000000000000 : ℝ)^3151
        have hw : |(2585597521/5000000000 : ℝ)|=(2585597521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1379983417/10000000000 : ℝ)|^4175 ≤ (1812564024513/25000000000000 : ℝ)^3151
        have hw : |(-1379983417/10000000000 : ℝ)|=(1379983417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3008500999/5000000000 : ℝ)|^4175 ≤ (5101336330901/10000000000000 : ℝ)^3151
        have hw : |(3008500999/5000000000 : ℝ)|=(3008500999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s0_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5171195021/10000000000 : ℝ)*x 0 + (6017002063/10000000000 : ℝ)*x 1 + (-86248959/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171195021/10000000000 : ℝ)^4175 ≤ (41736380357463/100000000000000 : ℝ)^3151 := by
    have hnat : (5171195021 : ℕ)^4175*100000000000000^3151 ≤ 41736380357463^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171195021 10000000000 41736380357463 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6017002063/10000000000 : ℝ)^4175 ≤ (25506682019591/50000000000000 : ℝ)^3151 := by
    have hnat : (6017002063 : ℕ)^4175*50000000000000^3151 ≤ 25506682019591^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017002063 10000000000 25506682019591 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86248959/625000000 : ℝ)^4175 ≤ (7250255589881/100000000000000 : ℝ)^3151 := by
    have hnat : (86248959 : ℕ)^4175*100000000000000^3151 ≤ 7250255589881^3151*625000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86248959 625000000 7250255589881 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171195021/10000000000 : ℝ), (6017002063/10000000000 : ℝ), (-86248959/625000000 : ℝ)] ![(41736380357463/100000000000000 : ℝ), (25506682019591/50000000000000 : ℝ), (7250255589881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171195021/10000000000 : ℝ)|^4175 ≤ (41736380357463/100000000000000 : ℝ)^3151
        have hw : |(5171195021/10000000000 : ℝ)|=(5171195021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6017002063/10000000000 : ℝ)|^4175 ≤ (25506682019591/50000000000000 : ℝ)^3151
        have hw : |(6017002063/10000000000 : ℝ)|=(6017002063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86248959/625000000 : ℝ)|^4175 ≤ (7250255589881/100000000000000 : ℝ)^3151
        have hw : |(-86248959/625000000 : ℝ)|=(86248959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s0_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4209959921/10000000000 : ℝ)*x 0 + (5586195589/10000000000 : ℝ)*x 1 + (63759419/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209959921/10000000000 : ℝ)^4175 ≤ (31781708624641/100000000000000 : ℝ)^3151 := by
    have hnat : (4209959921 : ℕ)^4175*100000000000000^3151 ≤ 31781708624641^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209959921 10000000000 31781708624641 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5586195589/10000000000 : ℝ)^4175 ≤ (9246234358859/20000000000000 : ℝ)^3151 := by
    have hnat : (5586195589 : ℕ)^4175*20000000000000^3151 ≤ 9246234358859^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586195589 10000000000 9246234358859 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63759419/200000000 : ℝ)^4175 ≤ (21987119564781/100000000000000 : ℝ)^3151 := by
    have hnat : (63759419 : ℕ)^4175*100000000000000^3151 ≤ 21987119564781^3151*200000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63759419 200000000 21987119564781 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209959921/10000000000 : ℝ), (5586195589/10000000000 : ℝ), (63759419/200000000 : ℝ)] ![(31781708624641/100000000000000 : ℝ), (9246234358859/20000000000000 : ℝ), (21987119564781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209959921/10000000000 : ℝ)|^4175 ≤ (31781708624641/100000000000000 : ℝ)^3151
        have hw : |(4209959921/10000000000 : ℝ)|=(4209959921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5586195589/10000000000 : ℝ)|^4175 ≤ (9246234358859/20000000000000 : ℝ)^3151
        have hw : |(5586195589/10000000000 : ℝ)|=(5586195589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63759419/200000000 : ℝ)|^4175 ≤ (21987119564781/100000000000000 : ℝ)^3151
        have hw : |(63759419/200000000 : ℝ)|=(63759419/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (19/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13879/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8349/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8349 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8349*1^2048 ≤ 0^2048*1^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8349/2048 : ℝ) ≤ (2386348248129444031/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8349 ≤ (2386348248129444031/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8349*100000000000000000000^2048 ≤ 2386348248129444031^2048*5^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2386348248129444031 100000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2386348248129444031/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8349 := by
      have hnat : (1 : ℕ)^2048*1^8349 ≤ 1^8349*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102386348248129444031/100000000000000000000 : ℝ) ≤ (5029008482752227/5000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (102386348248129444031/100000000000000000000 : ℝ)^2048 ≤ (5029008482752227/5000000000000000 : ℝ)^8349 := by
      have hnat : (102386348248129444031 : ℕ)^2048*5000000000000000^8349 ≤ 5029008482752227^8349*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102386348248129444031 100000000000000000000 5029008482752227 5000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029008482752227/5000000000000000 : ℝ)) (X := (102386348248129444031/100000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52386348248129444031/50000000000000000000 : ℝ) ≤ (2529008482752227/2500000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (52386348248129444031/50000000000000000000 : ℝ)^2048 ≤ (2529008482752227/2500000000000000 : ℝ)^8349 := by
      have hnat : (52386348248129444031 : ℕ)^2048*2500000000000000^8349 ≤ 2529008482752227^8349*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52386348248129444031 50000000000000000000 2529008482752227 2500000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529008482752227/2500000000000000 : ℝ)) (X := (52386348248129444031/50000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(29008482752227/2000000000000000 : ℝ)*(0 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29008482752227/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2386348248129444031/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(29008482752227/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (1 : ℝ)+(29008482752227/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5029008482752227/5000000000000000 : ℝ) by norm_num, show 1+(2386348248129444031/100000000000000000000 : ℝ)+(0 : ℝ)=(102386348248129444031/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2386348248129444031/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(29008482752227/2000000000000000 : ℝ)*(2/5 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29008482752227/2000000000000000 : ℝ)*(2/5 : ℝ)=(2529008482752227/2500000000000000 : ℝ) by norm_num, show 1+2*(2386348248129444031/100000000000000000000 : ℝ)=(52386348248129444031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(29008482752227/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29008482752227/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(29008482752227/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29008482752227/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(29008482752227/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29008482752227/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1887072367/10000000000 : ℝ)*X 0 0+(3025434877/5000000000 : ℝ)*X 0 1+(239118323/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((44127589/80000000 : ℝ)*X 1 0+(-52292379/200000000 : ℝ)*X 1 1+(1195591623/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103189721/2000000000 : ℝ)*X 2 0+(1195591627/2500000000 : ℝ)*X 2 1+(-522923791/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099890209/5000000000 : ℝ)*X 0 0+(3120393759/10000000000 : ℝ)*X 0 1+(5651475401/10000000000 : ℝ)*X 0 2+(2099890209/5000000000 : ℝ)*X 1 0+(3120393759/10000000000 : ℝ)*X 1 1+(5651475401/10000000000 : ℝ)*X 1 2+(2099890209/5000000000 : ℝ)*X 2 0+(3120393759/10000000000 : ℝ)*X 2 1+(5651475401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-946086969/5000000000 : ℝ)*X 0 0+(4815082671/10000000000 : ℝ)*X 0 1+(3008501093/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585597521/5000000000 : ℝ)*X 1 0+(-1379983417/10000000000 : ℝ)*X 1 1+(3008500999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171195021/10000000000 : ℝ)*X 2 0+(6017002063/10000000000 : ℝ)*X 2 1+(-86248959/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4209959921/10000000000 : ℝ)*X 0 0+(5586195589/10000000000 : ℝ)*X 0 1+(63759419/200000000 : ℝ)*X 0 2+(4209959921/10000000000 : ℝ)*X 1 0+(5586195589/10000000000 : ℝ)*X 1 1+(63759419/200000000 : ℝ)*X 1 2+(4209959921/10000000000 : ℝ)*X 2 0+(5586195589/10000000000 : ℝ)*X 2 1+(63759419/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126051362393377375721679/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13429463/25000000000000 : ℝ)*(base1) + (250772021/20000000000000 : ℝ)*(base19) + (1165192787/100000000000000 : ℝ)*(base23) + (85808929/100000000000000 : ℝ)*(base24) + (36039469/12500000000000 : ℝ)*(upper3) + (295857327422441/50000000000000 : ℝ)*(major0) + (295857327422441/50000000000000 : ℝ)*(major1) + (295857327422441/50000000000000 : ℝ)*(major2) + (394167427089309/50000000000000 : ℝ)*(sp0) + (788336322604347/100000000000000 : ℝ)*(sp1) + (49271020341421/6250000000000 : ℝ)*(sp2) + (49386162897973/12500000000000 : ℝ)*(sp3) + (2776003687/100000000000000 : ℝ)*(sp4) + (1104127593/50000000000000 : ℝ)*(sp7) + (197545782578411/50000000000000 : ℝ)*(f.failure) + (197084394116113/25000000000000 : ℝ)*(f.sum) + (23210372226107/50000000000000000000000000000 : ℝ)*base65 + (64108906626107/100000000000000000000000000000 : ℝ)*base67 + (255143947926107/100000000000000000000000000000 : ℝ)*base69 + (480738073226107/100000000000000000000000000000 : ℝ)*base71 + (85250585473893/50000000000000000000000000000 : ℝ)*base74 + (788051081726107/100000000000000000000000000000 : ℝ)*base75 + (444237032726107/100000000000000000000000000000 : ℝ)*base77 + (246817112726107/100000000000000000000000000000 : ℝ)*base79 + (180079597673893/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (29526529/5000000000000000000000 : ℝ)*base90 + (29526529/5000000000000000000000 : ℝ)*base92 + (29526529/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (193031748040765910193627/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5812729/6250000000000 : ℝ)*(base1) + (477975741/25000000000000 : ℝ)*(base19) + (381694261/20000000000000 : ℝ)*(base23) + (208609453/100000000000000 : ℝ)*(upper3) + (112502439/50000000000000 : ℝ)*(upper5) + (624488948816067/100000000000000 : ℝ)*(major0) + (624488948816067/100000000000000 : ℝ)*(major1) + (624488948816067/100000000000000 : ℝ)*(major2) + (3898309599/100000000000000 : ℝ)*(sp1) + (97437887/2500000000000 : ℝ)*(sp2) + (20800064190701/2500000000000 : ℝ)*(sp4) + (831996664411813/100000000000000 : ℝ)*(sp5) + (831996668637591/100000000000000 : ℝ)*(sp6) + (16679002905137/4000000000000 : ℝ)*(sp7) + (52121895704011/12500000000000 : ℝ)*(f.failure) + (104000309328047/12500000000000 : ℝ)*(f.sum) + (111551932868791/100000000000000000000000000000 : ℝ)*base66 + (1020361075368791/200000000000000000000000000000 : ℝ)*base68 + (62448480368791/200000000000000000000000000000 : ℝ)*base70 + (957726031568791/200000000000000000000000000000 : ℝ)*base72 + (336599767768791/100000000000000000000000000000 : ℝ)*base74 + (637458791231209/200000000000000000000000000000 : ℝ)*base75 + (113402510431209/200000000000000000000000000000 : ℝ)*base77 + (506800921968791/200000000000000000000000000000 : ℝ)*base80 + (238423246968791/100000000000000000000000000000 : ℝ)*base82 + (6524929/1250000000000000000000 : ℝ)*base90 + (6524929/1250000000000000000000 : ℝ)*base92 + (6524929/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1157_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (19/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13879/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1157_s1_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2090647957/10000000000 : ℝ)*x 0 + (5697526101/10000000000 : ℝ)*x 1 + (5005386681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090647957/10000000000 : ℝ)^4175 ≤ (12571537125703/100000000000000 : ℝ)^3151 := by
    have hnat : (2090647957 : ℕ)^4175*100000000000000^3151 ≤ 12571537125703^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090647957 10000000000 12571537125703 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5697526101/10000000000 : ℝ)^4175 ≤ (23727948878151/50000000000000 : ℝ)^3151 := by
    have hnat : (5697526101 : ℕ)^4175*50000000000000^3151 ≤ 23727948878151^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697526101 10000000000 23727948878151 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5005386681/10000000000 : ℝ)^4175 ≤ (7994513021377/20000000000000 : ℝ)^3151 := by
    have hnat : (5005386681 : ℕ)^4175*20000000000000^3151 ≤ 7994513021377^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005386681 10000000000 7994513021377 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2090647957/10000000000 : ℝ), (5697526101/10000000000 : ℝ), (5005386681/10000000000 : ℝ)] ![(12571537125703/100000000000000 : ℝ), (23727948878151/50000000000000 : ℝ), (7994513021377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2090647957/10000000000 : ℝ)|^4175 ≤ (12571537125703/100000000000000 : ℝ)^3151
        have hw : |(-2090647957/10000000000 : ℝ)|=(2090647957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5697526101/10000000000 : ℝ)|^4175 ≤ (23727948878151/50000000000000 : ℝ)^3151
        have hw : |(5697526101/10000000000 : ℝ)|=(5697526101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5005386681/10000000000 : ℝ)|^4175 ≤ (7994513021377/20000000000000 : ℝ)^3151
        have hw : |(5005386681/10000000000 : ℝ)|=(5005386681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s1_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1354575321/2500000000 : ℝ)*x 0 + (-615970213/2500000000 : ℝ)*x 1 + (1251346441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354575321/2500000000 : ℝ)^4175 ≤ (22199593035849/50000000000000 : ℝ)^3151 := by
    have hnat : (1354575321 : ℕ)^4175*50000000000000^3151 ≤ 22199593035849^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354575321 2500000000 22199593035849 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (615970213/2500000000 : ℝ)^4175 ≤ (15628258511211/100000000000000 : ℝ)^3151 := by
    have hnat : (615970213 : ℕ)^4175*100000000000000^3151 ≤ 15628258511211^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615970213 2500000000 15628258511211 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251346441/2500000000 : ℝ)^4175 ≤ (1998627770199/5000000000000 : ℝ)^3151 := by
    have hnat : (1251346441 : ℕ)^4175*5000000000000^3151 ≤ 1998627770199^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251346441 2500000000 1998627770199 5000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354575321/2500000000 : ℝ), (-615970213/2500000000 : ℝ), (1251346441/2500000000 : ℝ)] ![(22199593035849/50000000000000 : ℝ), (15628258511211/100000000000000 : ℝ), (1998627770199/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354575321/2500000000 : ℝ)|^4175 ≤ (22199593035849/50000000000000 : ℝ)^3151
        have hw : |(1354575321/2500000000 : ℝ)|=(1354575321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-615970213/2500000000 : ℝ)|^4175 ≤ (15628258511211/100000000000000 : ℝ)^3151
        have hw : |(-615970213/2500000000 : ℝ)|=(615970213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251346441/2500000000 : ℝ)|^4175 ≤ (1998627770199/5000000000000 : ℝ)^3151
        have hw : |(1251346441/2500000000 : ℝ)|=(1251346441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s1_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (338643961/625000000 : ℝ)*x 0 + (125134597/250000000 : ℝ)*x 1 + (-1231940261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338643961/625000000 : ℝ)^4175 ≤ (44399208785071/100000000000000 : ℝ)^3151 := by
    have hnat : (338643961 : ℕ)^4175*100000000000000^3151 ≤ 44399208785071^3151*625000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338643961 625000000 44399208785071 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125134597/250000000 : ℝ)^4175 ≤ (19986267734557/50000000000000 : ℝ)^3151 := by
    have hnat : (125134597 : ℕ)^4175*50000000000000^3151 ≤ 19986267734557^3151*250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125134597 250000000 19986267734557 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231940261/5000000000 : ℝ)^4175 ≤ (15628255737809/100000000000000 : ℝ)^3151 := by
    have hnat : (1231940261 : ℕ)^4175*100000000000000^3151 ≤ 15628255737809^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231940261 5000000000 15628255737809 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338643961/625000000 : ℝ), (125134597/250000000 : ℝ), (-1231940261/5000000000 : ℝ)] ![(44399208785071/100000000000000 : ℝ), (19986267734557/50000000000000 : ℝ), (15628255737809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338643961/625000000 : ℝ)|^4175 ≤ (44399208785071/100000000000000 : ℝ)^3151
        have hw : |(338643961/625000000 : ℝ)|=(338643961/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125134597/250000000 : ℝ)|^4175 ≤ (19986267734557/50000000000000 : ℝ)^3151
        have hw : |(125134597/250000000 : ℝ)|=(125134597/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1231940261/5000000000 : ℝ)|^4175 ≤ (15628255737809/100000000000000 : ℝ)^3151
        have hw : |(-1231940261/5000000000 : ℝ)|=(1231940261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s1_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863232849/2000000000 : ℝ)*x 0 + (3679834661/10000000000 : ℝ)*x 1 + (1265219171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863232849/2000000000 : ℝ)^4175 ≤ (32848344443777/100000000000000 : ℝ)^3151 := by
    have hnat : (863232849 : ℕ)^4175*100000000000000^3151 ≤ 32848344443777^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863232849 2000000000 32848344443777 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3679834661/10000000000 : ℝ)^4175 ≤ (13295443954459/50000000000000 : ℝ)^3151 := by
    have hnat : (3679834661 : ℕ)^4175*50000000000000^3151 ≤ 13295443954459^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679834661 10000000000 13295443954459 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1265219171/2500000000 : ℝ)^4175 ≤ (40560767631919/100000000000000 : ℝ)^3151 := by
    have hnat : (1265219171 : ℕ)^4175*100000000000000^3151 ≤ 40560767631919^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265219171 2500000000 40560767631919 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863232849/2000000000 : ℝ), (3679834661/10000000000 : ℝ), (1265219171/2500000000 : ℝ)] ![(32848344443777/100000000000000 : ℝ), (13295443954459/50000000000000 : ℝ), (40560767631919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863232849/2000000000 : ℝ)|^4175 ≤ (32848344443777/100000000000000 : ℝ)^3151
        have hw : |(863232849/2000000000 : ℝ)|=(863232849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3679834661/10000000000 : ℝ)|^4175 ≤ (13295443954459/50000000000000 : ℝ)^3151
        have hw : |(3679834661/10000000000 : ℝ)|=(3679834661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1265219171/2500000000 : ℝ)|^4175 ≤ (40560767631919/100000000000000 : ℝ)^3151
        have hw : |(1265219171/2500000000 : ℝ)|=(1265219171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s1_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045718983/5000000000 : ℝ)*x 0 + (5014783499/10000000000 : ℝ)*x 1 + (2843970421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045718983/5000000000 : ℝ)^4175 ≤ (3144457953583/25000000000000 : ℝ)^3151 := by
    have hnat : (1045718983 : ℕ)^4175*25000000000000^3151 ≤ 3144457953583^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045718983 5000000000 3144457953583 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014783499/10000000000 : ℝ)^4175 ≤ (40072024471503/100000000000000 : ℝ)^3151 := by
    have hnat : (5014783499 : ℕ)^4175*100000000000000^3151 ≤ 40072024471503^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014783499 10000000000 40072024471503 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2843970421/5000000000 : ℝ)^4175 ≤ (11837535925977/25000000000000 : ℝ)^3151 := by
    have hnat : (2843970421 : ℕ)^4175*25000000000000^3151 ≤ 11837535925977^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843970421 5000000000 11837535925977 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045718983/5000000000 : ℝ), (5014783499/10000000000 : ℝ), (2843970421/5000000000 : ℝ)] ![(3144457953583/25000000000000 : ℝ), (40072024471503/100000000000000 : ℝ), (11837535925977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045718983/5000000000 : ℝ)|^4175 ≤ (3144457953583/25000000000000 : ℝ)^3151
        have hw : |(-1045718983/5000000000 : ℝ)|=(1045718983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5014783499/10000000000 : ℝ)|^4175 ≤ (40072024471503/100000000000000 : ℝ)^3151
        have hw : |(5014783499/10000000000 : ℝ)|=(5014783499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2843970421/5000000000 : ℝ)|^4175 ≤ (11837535925977/25000000000000 : ℝ)^3151
        have hw : |(2843970421/5000000000 : ℝ)|=(2843970421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s1_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5240716031/10000000000 : ℝ)*x 0 + (-1781321943/10000000000 : ℝ)*x 1 + (2843972171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240716031/10000000000 : ℝ)^4175 ≤ (1062036077081/2500000000000 : ℝ)^3151 := by
    have hnat : (5240716031 : ℕ)^4175*2500000000000^3151 ≤ 1062036077081^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240716031 10000000000 1062036077081 2500000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1781321943/10000000000 : ℝ)^4175 ≤ (5084187302189/50000000000000 : ℝ)^3151 := by
    have hnat : (1781321943 : ℕ)^4175*50000000000000^3151 ≤ 5084187302189^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781321943 10000000000 5084187302189 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2843972171/5000000000 : ℝ)^4175 ≤ (9470036461761/20000000000000 : ℝ)^3151 := by
    have hnat : (2843972171 : ℕ)^4175*20000000000000^3151 ≤ 9470036461761^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843972171 5000000000 9470036461761 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240716031/10000000000 : ℝ), (-1781321943/10000000000 : ℝ), (2843972171/5000000000 : ℝ)] ![(1062036077081/2500000000000 : ℝ), (5084187302189/50000000000000 : ℝ), (9470036461761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240716031/10000000000 : ℝ)|^4175 ≤ (1062036077081/2500000000000 : ℝ)^3151
        have hw : |(5240716031/10000000000 : ℝ)|=(5240716031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1781321943/10000000000 : ℝ)|^4175 ≤ (5084187302189/50000000000000 : ℝ)^3151
        have hw : |(-1781321943/10000000000 : ℝ)|=(1781321943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2843972171/5000000000 : ℝ)|^4175 ≤ (9470036461761/20000000000000 : ℝ)^3151
        have hw : |(2843972171/5000000000 : ℝ)|=(2843972171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s1_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1310178733/2500000000 : ℝ)*x 0 + (355496621/625000000 : ℝ)*x 1 + (-1781321179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310178733/2500000000 : ℝ)^4175 ≤ (42481431279643/100000000000000 : ℝ)^3151 := by
    have hnat : (1310178733 : ℕ)^4175*100000000000000^3151 ≤ 42481431279643^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310178733 2500000000 42481431279643 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355496621/625000000 : ℝ)^4175 ≤ (2367509994529/5000000000000 : ℝ)^3151 := by
    have hnat : (355496621 : ℕ)^4175*5000000000000^3151 ≤ 2367509994529^3151*625000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355496621 625000000 2367509994529 5000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1781321179/10000000000 : ℝ)^4175 ≤ (10168368825939/100000000000000 : ℝ)^3151 := by
    have hnat : (1781321179 : ℕ)^4175*100000000000000^3151 ≤ 10168368825939^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781321179 10000000000 10168368825939 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310178733/2500000000 : ℝ), (355496621/625000000 : ℝ), (-1781321179/10000000000 : ℝ)] ![(42481431279643/100000000000000 : ℝ), (2367509994529/5000000000000 : ℝ), (10168368825939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310178733/2500000000 : ℝ)|^4175 ≤ (42481431279643/100000000000000 : ℝ)^3151
        have hw : |(1310178733/2500000000 : ℝ)|=(1310178733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355496621/625000000 : ℝ)|^4175 ≤ (2367509994529/5000000000000 : ℝ)^3151
        have hw : |(355496621/625000000 : ℝ)|=(355496621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1781321179/10000000000 : ℝ)|^4175 ≤ (10168368825939/100000000000000 : ℝ)^3151
        have hw : |(-1781321179/10000000000 : ℝ)|=(1781321179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s1_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539716133/1250000000 : ℝ)*x 0 + (1008425701/2000000000 : ℝ)*x 1 + (3698951703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539716133/1250000000 : ℝ)^4175 ≤ (32864124672437/100000000000000 : ℝ)^3151 := by
    have hnat : (539716133 : ℕ)^4175*100000000000000^3151 ≤ 32864124672437^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539716133 1250000000 32864124672437 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008425701/2000000000 : ℝ)^4175 ≤ (40361798428561/100000000000000 : ℝ)^3151 := by
    have hnat : (1008425701 : ℕ)^4175*100000000000000^3151 ≤ 40361798428561^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008425701 2000000000 40361798428561 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3698951703/10000000000 : ℝ)^4175 ≤ (6693519220433/25000000000000 : ℝ)^3151 := by
    have hnat : (3698951703 : ℕ)^4175*25000000000000^3151 ≤ 6693519220433^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698951703 10000000000 6693519220433 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539716133/1250000000 : ℝ), (1008425701/2000000000 : ℝ), (3698951703/10000000000 : ℝ)] ![(32864124672437/100000000000000 : ℝ), (40361798428561/100000000000000 : ℝ), (6693519220433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539716133/1250000000 : ℝ)|^4175 ≤ (32864124672437/100000000000000 : ℝ)^3151
        have hw : |(539716133/1250000000 : ℝ)|=(539716133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008425701/2000000000 : ℝ)|^4175 ≤ (40361798428561/100000000000000 : ℝ)^3151
        have hw : |(1008425701/2000000000 : ℝ)|=(1008425701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3698951703/10000000000 : ℝ)|^4175 ≤ (6693519220433/25000000000000 : ℝ)^3151
        have hw : |(3698951703/10000000000 : ℝ)|=(3698951703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13879/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (19/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5733/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2037/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13879/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (19/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13879/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (19/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13879/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (19/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13879/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (19/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13879/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (19/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13879/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (19/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (19/4000 : ℝ) ^ (8349/2048 : ℝ) ≤ (16890379669/50000000000000000000 : ℝ) := by
    have hpowers : (19/4000 : ℝ)^8349 ≤ (16890379669/50000000000000000000 : ℝ)^2048 := by
      have hnat : (19 : ℕ)^8349*50000000000000000000^2048 ≤ 16890379669^2048*4000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19 4000 16890379669 50000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19/4000 : ℝ)) (X := (16890379669/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13879/50000 : ℝ) ^ (8349/2048 : ℝ) ≤ (107624892736645827/20000000000000000000 : ℝ) := by
    have hpowers : (13879/50000 : ℝ)^8349 ≤ (107624892736645827/20000000000000000000 : ℝ)^2048 := by
      have hnat : (13879 : ℕ)^8349*20000000000000000000^2048 ≤ 107624892736645827^2048*50000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13879 50000 107624892736645827 20000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13879/50000 : ℝ)) (X := (107624892736645827/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000016890379669/25000000000000000000 : ℝ) ≤ (10000000001657277/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (25000000016890379669/25000000000000000000 : ℝ)^2048 ≤ (10000000001657277/10000000000000000 : ℝ)^8349 := by
      have hnat : (25000000016890379669 : ℕ)^2048*10000000000000000^8349 ≤ 10000000001657277^8349*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000016890379669 25000000000000000000 10000000001657277 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001657277/10000000000000000 : ℝ)) (X := (25000000016890379669/25000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100538124497463988473/100000000000000000000 : ℝ) ≤ (10013173411060937/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (100538124497463988473/100000000000000000000 : ℝ)^2048 ≤ (10013173411060937/10000000000000000 : ℝ)^8349 := by
      have hnat : (100538124497463988473 : ℕ)^2048*10000000000000000^8349 ≤ 10013173411060937^8349*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100538124497463988473 100000000000000000000 10013173411060937 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013173411060937/10000000000000000 : ℝ)) (X := (100538124497463988473/100000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10107624892736645827/10000000000000000000 : ℝ) ≤ (10026346820464597/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (10107624892736645827/10000000000000000000 : ℝ)^2048 ≤ (10026346820464597/10000000000000000 : ℝ)^8349 := by
      have hnat : (10107624892736645827 : ℕ)^2048*10000000000000000^8349 ≤ 10026346820464597^8349*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10107624892736645827 10000000000000000000 10026346820464597 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026346820464597/10000000000000000 : ℝ)) (X := (10107624892736645827/10000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(16890379669/50000000000000000000 : ℝ) ≤ ((272817485306282011391/272830000000000000000 : ℝ)+2*(658670470183/136415000000000 : ℝ)*(19/4000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (272817485306282011391/272830000000000000000 : ℝ)+2*(658670470183/136415000000000 : ℝ)*(19/4000 : ℝ)=(10000000001657277/10000000000000000 : ℝ) by norm_num, show 1+2*(16890379669/50000000000000000000 : ℝ)=(25000000016890379669/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(107624892736645827/20000000000000000000 : ℝ)+(16890379669/50000000000000000000 : ℝ) ≤ ((272817485306282011391/272830000000000000000 : ℝ)+(658670470183/136415000000000 : ℝ)*((13879/50000 : ℝ)+(19/4000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (272817485306282011391/272830000000000000000 : ℝ)+(658670470183/136415000000000 : ℝ)*((13879/50000 : ℝ)+(19/4000 : ℝ))=(10013173411060937/10000000000000000 : ℝ) by norm_num, show 1+(107624892736645827/20000000000000000000 : ℝ)+(16890379669/50000000000000000000 : ℝ)=(100538124497463988473/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(107624892736645827/20000000000000000000 : ℝ) ≤ ((272817485306282011391/272830000000000000000 : ℝ)+2*(658670470183/136415000000000 : ℝ)*(13879/50000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (272817485306282011391/272830000000000000000 : ℝ)+2*(658670470183/136415000000000 : ℝ)*(13879/50000 : ℝ)=(10026346820464597/10000000000000000 : ℝ) by norm_num, show 1+2*(107624892736645827/20000000000000000000 : ℝ)=(10107624892736645827/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (272817485306282011391/272830000000000000000 : ℝ)*(X 1 0+X 2 0)+(658670470183/136415000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (19/4000 : ℝ)) (hi := (13879/50000 : ℝ)) (c := (272817485306282011391/272830000000000000000 : ℝ)) (alpha := (658670470183/136415000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (272817485306282011391/272830000000000000000 : ℝ)*(X 0 1+X 2 1)+(658670470183/136415000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (19/4000 : ℝ)) (hi := (13879/50000 : ℝ)) (c := (272817485306282011391/272830000000000000000 : ℝ)) (alpha := (658670470183/136415000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (272817485306282011391/272830000000000000000 : ℝ)*(X 0 2+X 1 2)+(658670470183/136415000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (19/4000 : ℝ)) (hi := (13879/50000 : ℝ)) (c := (272817485306282011391/272830000000000000000 : ℝ)) (alpha := (658670470183/136415000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2090647957/10000000000 : ℝ)*X 0 0+(5697526101/10000000000 : ℝ)*X 0 1+(5005386681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1354575321/2500000000 : ℝ)*X 1 0+(-615970213/2500000000 : ℝ)*X 1 1+(1251346441/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((338643961/625000000 : ℝ)*X 2 0+(125134597/250000000 : ℝ)*X 2 1+(-1231940261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863232849/2000000000 : ℝ)*X 0 0+(3679834661/10000000000 : ℝ)*X 0 1+(1265219171/2500000000 : ℝ)*X 0 2+(863232849/2000000000 : ℝ)*X 1 0+(3679834661/10000000000 : ℝ)*X 1 1+(1265219171/2500000000 : ℝ)*X 1 2+(863232849/2000000000 : ℝ)*X 2 0+(3679834661/10000000000 : ℝ)*X 2 1+(1265219171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1045718983/5000000000 : ℝ)*X 0 0+(5014783499/10000000000 : ℝ)*X 0 1+(2843970421/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5240716031/10000000000 : ℝ)*X 1 0+(-1781321943/10000000000 : ℝ)*X 1 1+(2843972171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1310178733/2500000000 : ℝ)*X 2 0+(355496621/625000000 : ℝ)*X 2 1+(-1781321179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539716133/1250000000 : ℝ)*X 0 0+(1008425701/2000000000 : ℝ)*X 0 1+(3698951703/10000000000 : ℝ)*X 0 2+(539716133/1250000000 : ℝ)*X 1 0+(1008425701/2000000000 : ℝ)*X 1 1+(3698951703/10000000000 : ℝ)*X 1 2+(539716133/1250000000 : ℝ)*X 2 0+(1008425701/2000000000 : ℝ)*X 2 1+(3698951703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29907044630040967364511434799/6820750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59594217/12500000000000 : ℝ)*(base1) + (617843227/100000000000000 : ℝ)*(base19) + (1212867459/100000000000000 : ℝ)*(base23) + (328488493/100000000000000 : ℝ)*(base37) + (8183/97656250000 : ℝ)*(lower2) + (1084442083220727/100000000000000 : ℝ)*(major0) + (1084442083220727/100000000000000 : ℝ)*(major1) + (135555260402591/12500000000000 : ℝ)*(major2) + (144479506471553/10000000000000 : ℝ)*(sp0) + (1444793053973837/100000000000000 : ℝ)*(sp1) + (144479406553173/10000000000000 : ℝ)*(sp2) + (45255496040179/6250000000000 : ℝ)*(sp3) + (345218697/50000000000000 : ℝ)*(sp4) + (12852657/800000000000 : ℝ)*(sp5) + (181022185471273/25000000000000 : ℝ)*(f.failure) + (1444795278399189/100000000000000 : ℝ)*(f.sum) + (8319463886637/6820750000000000000000000000 : ℝ)*base66 + (86885933241490698743/27283000000000000000000000000000000 : ℝ)*base68 + (30372368541782914081/3410375000000000000000000000000000 : ℝ)*base69 + (195252127341999698743/27283000000000000000000000000000000 : ℝ)*base72 + (9631307397037/5456600000000000000000000000 : ℝ)*base74 + (9542338449805414081/3410375000000000000000000000000000 : ℝ)*base75 + (141159547716216698743/27283000000000000000000000000000000 : ℝ)*base78 + (310060507050568698743/27283000000000000000000000000000000 : ℝ)*base80 + (504899223873/852593750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (625147/2500000000000000000000 : ℝ)*base90 + (625147/2500000000000000000000 : ℝ)*base92 + (25625147/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19684695564550386934219023747/6820750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1249042291/50000000000000 : ℝ)*(base19) + (3159647319/100000000000000 : ℝ)*(base23) + (39964187/10000000000000 : ℝ)*(upper2) + (642872177/100000000000000 : ℝ)*(upper3) + (179164071/50000000000000 : ℝ)*(upper5) + (557508878839013/50000000000000 : ℝ)*(major0) + (557508878839013/50000000000000 : ℝ)*(major1) + (557508878839013/50000000000000 : ℝ)*(major2) + (13980509771/100000000000000 : ℝ)*(sp1) + (252407423/1250000000000 : ℝ)*(sp2) + (185691388594541/12500000000000 : ℝ)*(sp4) + (185689328770247/12500000000000 : ℝ)*(sp5) + (1485507756515169/100000000000000 : ℝ)*(sp6) + (744504310399661/100000000000000 : ℝ)*(sp7) + (744504310399661/100000000000000 : ℝ)*(f.failure) + (185691388594541/12500000000000 : ℝ)*(f.sum) + (3109634426249/1705187500000000000000000000 : ℝ)*base65 + (95597698611716302917/13641500000000000000000000000000000 : ℝ)*base68 + (189533782180769302917/13641500000000000000000000000000000 : ℝ)*base70 + (172195567525866802917/13641500000000000000000000000000000 : ℝ)*base72 + (25797109789797/27283000000000000000000000000 : ℝ)*base73 + (234576537260659302917/13641500000000000000000000000000000 : ℝ)*base76 + (76676749517978802917/13641500000000000000000000000000000 : ℝ)*base78 + (55941458579464302917/13641500000000000000000000000000000 : ℝ)*base80 + (12624504123423/3410375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (123569721/10000000000000000000000 : ℝ)*base89 + (123569721/10000000000000000000000 : ℝ)*base91 + (123569721/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1157_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13879/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (19/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5733/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2037/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1157_s2_0 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53577/250000 : ℝ)*x 0 + (1376996463/2500000000 : ℝ)*x 1 + (1032314323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53577/250000 : ℝ)^4175 ≤ (811936000111/6250000000000 : ℝ)^3151 := by
    have hnat : (53577 : ℕ)^4175*6250000000000^3151 ≤ 811936000111^3151*250000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53577 250000 811936000111 6250000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376996463/2500000000 : ℝ)^4175 ≤ (45375523247571/100000000000000 : ℝ)^3151 := by
    have hnat : (1376996463 : ℕ)^4175*100000000000000^3151 ≤ 45375523247571^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376996463 2500000000 45375523247571 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032314323/2000000000 : ℝ)^4175 ≤ (41633500737481/100000000000000 : ℝ)^3151 := by
    have hnat : (1032314323 : ℕ)^4175*100000000000000^3151 ≤ 41633500737481^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032314323 2000000000 41633500737481 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53577/250000 : ℝ), (1376996463/2500000000 : ℝ), (1032314323/2000000000 : ℝ)] ![(811936000111/6250000000000 : ℝ), (45375523247571/100000000000000 : ℝ), (41633500737481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53577/250000 : ℝ)|^4175 ≤ (811936000111/6250000000000 : ℝ)^3151
        have hw : |(-53577/250000 : ℝ)|=(53577/250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376996463/2500000000 : ℝ)|^4175 ≤ (45375523247571/100000000000000 : ℝ)^3151
        have hw : |(1376996463/2500000000 : ℝ)|=(1376996463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032314323/2000000000 : ℝ)|^4175 ≤ (41633500737481/100000000000000 : ℝ)^3151
        have hw : |(1032314323/2000000000 : ℝ)|=(1032314323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s2_1 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343306079/2500000000 : ℝ)*x 0 + (-464615289/2000000000 : ℝ)*x 1 + (258078703/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343306079/2500000000 : ℝ)^4175 ≤ (43910436882509/100000000000000 : ℝ)^3151 := by
    have hnat : (1343306079 : ℕ)^4175*100000000000000^3151 ≤ 43910436882509^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343306079 2500000000 43910436882509 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464615289/2000000000 : ℝ)^4175 ≤ (14456036234447/100000000000000 : ℝ)^3151 := by
    have hnat : (464615289 : ℕ)^4175*100000000000000^3151 ≤ 14456036234447^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464615289 2000000000 14456036234447 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258078703/500000000 : ℝ)^4175 ≤ (20816763433997/50000000000000 : ℝ)^3151 := by
    have hnat : (258078703 : ℕ)^4175*50000000000000^3151 ≤ 20816763433997^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258078703 500000000 20816763433997 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343306079/2500000000 : ℝ), (-464615289/2000000000 : ℝ), (258078703/500000000 : ℝ)] ![(43910436882509/100000000000000 : ℝ), (14456036234447/100000000000000 : ℝ), (20816763433997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343306079/2500000000 : ℝ)|^4175 ≤ (43910436882509/100000000000000 : ℝ)^3151
        have hw : |(1343306079/2500000000 : ℝ)|=(1343306079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-464615289/2000000000 : ℝ)|^4175 ≤ (14456036234447/100000000000000 : ℝ)^3151
        have hw : |(-464615289/2000000000 : ℝ)|=(464615289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258078703/500000000 : ℝ)|^4175 ≤ (20816763433997/50000000000000 : ℝ)^3151
        have hw : |(258078703/500000000 : ℝ)|=(258078703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s2_2 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343306137/2500000000 : ℝ)*x 0 + (5161573557/10000000000 : ℝ)*x 1 + (-290384599/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343306137/2500000000 : ℝ)^4175 ≤ (43910439394563/100000000000000 : ℝ)^3151 := by
    have hnat : (1343306137 : ℕ)^4175*100000000000000^3151 ≤ 43910439394563^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343306137 2500000000 43910439394563 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5161573557/10000000000 : ℝ)^4175 ≤ (41633521492269/100000000000000 : ℝ)^3151 := by
    have hnat : (5161573557 : ℕ)^4175*100000000000000^3151 ≤ 41633521492269^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161573557 10000000000 41633521492269 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290384599/1250000000 : ℝ)^4175 ≤ (14456039095483/100000000000000 : ℝ)^3151 := by
    have hnat : (290384599 : ℕ)^4175*100000000000000^3151 ≤ 14456039095483^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290384599 1250000000 14456039095483 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343306137/2500000000 : ℝ), (5161573557/10000000000 : ℝ), (-290384599/1250000000 : ℝ)] ![(43910439394563/100000000000000 : ℝ), (41633521492269/100000000000000 : ℝ), (14456039095483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343306137/2500000000 : ℝ)|^4175 ≤ (43910439394563/100000000000000 : ℝ)^3151
        have hw : |(1343306137/2500000000 : ℝ)|=(1343306137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5161573557/10000000000 : ℝ)|^4175 ≤ (41633521492269/100000000000000 : ℝ)^3151
        have hw : |(5161573557/10000000000 : ℝ)|=(5161573557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-290384599/1250000000 : ℝ)|^4175 ≤ (14456039095483/100000000000000 : ℝ)^3151
        have hw : |(-290384599/1250000000 : ℝ)|=(290384599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s2_3 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4352171437/10000000000 : ℝ)*x 0 + (8040241/20000000 : ℝ)*x 1 + (235566303/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352171437/10000000000 : ℝ)^4175 ≤ (6642384901307/20000000000000 : ℝ)^3151 := by
    have hnat : (4352171437 : ℕ)^4175*20000000000000^3151 ≤ 6642384901307^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352171437 10000000000 6642384901307 20000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8040241/20000000 : ℝ)^4175 ≤ (29896902069023/100000000000000 : ℝ)^3151 := by
    have hnat : (8040241 : ℕ)^4175*100000000000000^3151 ≤ 29896902069023^3151*20000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8040241 20000000 29896902069023 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235566303/500000000 : ℝ)^4175 ≤ (1844558670581/5000000000000 : ℝ)^3151 := by
    have hnat : (235566303 : ℕ)^4175*5000000000000^3151 ≤ 1844558670581^3151*500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235566303 500000000 1844558670581 5000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352171437/10000000000 : ℝ), (8040241/20000000 : ℝ), (235566303/500000000 : ℝ)] ![(6642384901307/20000000000000 : ℝ), (29896902069023/100000000000000 : ℝ), (1844558670581/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352171437/10000000000 : ℝ)|^4175 ≤ (6642384901307/20000000000000 : ℝ)^3151
        have hw : |(4352171437/10000000000 : ℝ)|=(4352171437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8040241/20000000 : ℝ)|^4175 ≤ (29896902069023/100000000000000 : ℝ)^3151
        have hw : |(8040241/20000000 : ℝ)|=(8040241/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235566303/500000000 : ℝ)|^4175 ≤ (1844558670581/5000000000000 : ℝ)^3151
        have hw : |(235566303/500000000 : ℝ)|=(235566303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s2_4 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214317799/1000000000 : ℝ)*x 0 + (516393607/1000000000 : ℝ)*x 1 + (5505598343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214317799/1000000000 : ℝ)^4175 ≤ (12991763041147/100000000000000 : ℝ)^3151 := by
    have hnat : (214317799 : ℕ)^4175*100000000000000^3151 ≤ 12991763041147^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214317799 1000000000 12991763041147 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516393607/1000000000 : ℝ)^4175 ≤ (20829386159573/50000000000000 : ℝ)^3151 := by
    have hnat : (516393607 : ℕ)^4175*50000000000000^3151 ≤ 20829386159573^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516393607 1000000000 20829386159573 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505598343/10000000000 : ℝ)^4175 ≤ (22674732316223/50000000000000 : ℝ)^3151 := by
    have hnat : (5505598343 : ℕ)^4175*50000000000000^3151 ≤ 22674732316223^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505598343 10000000000 22674732316223 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214317799/1000000000 : ℝ), (516393607/1000000000 : ℝ), (5505598343/10000000000 : ℝ)] ![(12991763041147/100000000000000 : ℝ), (20829386159573/50000000000000 : ℝ), (22674732316223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214317799/1000000000 : ℝ)|^4175 ≤ (12991763041147/100000000000000 : ℝ)^3151
        have hw : |(-214317799/1000000000 : ℝ)|=(214317799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516393607/1000000000 : ℝ)|^4175 ≤ (20829386159573/50000000000000 : ℝ)^3151
        have hw : |(516393607/1000000000 : ℝ)|=(516393607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505598343/10000000000 : ℝ)|^4175 ≤ (22674732316223/50000000000000 : ℝ)^3151
        have hw : |(5505598343/10000000000 : ℝ)|=(5505598343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s2_5 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057048427/2000000000 : ℝ)*x 0 + (-197905113/1000000000 : ℝ)*x 1 + (5505598333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057048427/2000000000 : ℝ)^4175 ≤ (42960326070261/100000000000000 : ℝ)^3151 := by
    have hnat : (1057048427 : ℕ)^4175*100000000000000^3151 ≤ 42960326070261^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057048427 2000000000 42960326070261 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197905113/1000000000 : ℝ)^4175 ≤ (11690209388541/100000000000000 : ℝ)^3151 := by
    have hnat : (197905113 : ℕ)^4175*100000000000000^3151 ≤ 11690209388541^3151*1000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197905113 1000000000 11690209388541 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5505598333/10000000000 : ℝ)^4175 ≤ (11337366130827/25000000000000 : ℝ)^3151 := by
    have hnat : (5505598333 : ℕ)^4175*25000000000000^3151 ≤ 11337366130827^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505598333 10000000000 11337366130827 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057048427/2000000000 : ℝ), (-197905113/1000000000 : ℝ), (5505598333/10000000000 : ℝ)] ![(42960326070261/100000000000000 : ℝ), (11690209388541/100000000000000 : ℝ), (11337366130827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057048427/2000000000 : ℝ)|^4175 ≤ (42960326070261/100000000000000 : ℝ)^3151
        have hw : |(1057048427/2000000000 : ℝ)|=(1057048427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197905113/1000000000 : ℝ)|^4175 ≤ (11690209388541/100000000000000 : ℝ)^3151
        have hw : |(-197905113/1000000000 : ℝ)|=(197905113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5505598333/10000000000 : ℝ)|^4175 ≤ (11337366130827/25000000000000 : ℝ)^3151
        have hw : |(5505598333/10000000000 : ℝ)|=(5505598333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s2_6 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057048449/2000000000 : ℝ)*x 0 + (2752799163/5000000000 : ℝ)*x 1 + (-494762747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057048449/2000000000 : ℝ)^4175 ≤ (10740081813737/25000000000000 : ℝ)^3151 := by
    have hnat : (1057048449 : ℕ)^4175*25000000000000^3151 ≤ 10740081813737^3151*2000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057048449 2000000000 10740081813737 25000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752799163/5000000000 : ℝ)^4175 ≤ (708585381983/1562500000000 : ℝ)^3151 := by
    have hnat : (2752799163 : ℕ)^4175*1562500000000^3151 ≤ 708585381983^3151*5000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752799163 5000000000 708585381983 1562500000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494762747/2500000000 : ℝ)^4175 ≤ (11690208277163/100000000000000 : ℝ)^3151 := by
    have hnat : (494762747 : ℕ)^4175*100000000000000^3151 ≤ 11690208277163^3151*2500000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494762747 2500000000 11690208277163 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057048449/2000000000 : ℝ), (2752799163/5000000000 : ℝ), (-494762747/2500000000 : ℝ)] ![(10740081813737/25000000000000 : ℝ), (708585381983/1562500000000 : ℝ), (11690208277163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057048449/2000000000 : ℝ)|^4175 ≤ (10740081813737/25000000000000 : ℝ)^3151
        have hw : |(1057048449/2000000000 : ℝ)|=(1057048449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752799163/5000000000 : ℝ)|^4175 ≤ (708585381983/1562500000000 : ℝ)^3151
        have hw : |(2752799163/5000000000 : ℝ)|=(2752799163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494762747/2500000000 : ℝ)|^4175 ≤ (11690208277163/100000000000000 : ℝ)^3151
        have hw : |(-494762747/2500000000 : ℝ)|=(494762747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1157_s2_7 (p : ℝ) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544046067/1250000000 : ℝ)*x 0 + (4706610521/10000000000 : ℝ)*x 1 + (503110197/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544046067/1250000000 : ℝ)^4175 ≤ (3321391739843/10000000000000 : ℝ)^3151 := by
    have hnat : (544046067 : ℕ)^4175*10000000000000^3151 ≤ 3321391739843^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544046067 1250000000 3321391739843 10000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4706610521/10000000000 : ℝ)^4175 ≤ (18421128867081/50000000000000 : ℝ)^3151 := by
    have hnat : (4706610521 : ℕ)^4175*50000000000000^3151 ≤ 18421128867081^3151*10000000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706610521 10000000000 18421128867081 50000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503110197/1250000000 : ℝ)^4175 ≤ (29943824861769/100000000000000 : ℝ)^3151 := by
    have hnat : (503110197 : ℕ)^4175*100000000000000^3151 ≤ 29943824861769^3151*1250000000^4175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503110197 1250000000 29943824861769 100000000000000 4175 3151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4175/1024 : ℝ)) 4175 3151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544046067/1250000000 : ℝ), (4706610521/10000000000 : ℝ), (503110197/1250000000 : ℝ)] ![(3321391739843/10000000000000 : ℝ), (18421128867081/50000000000000 : ℝ), (29943824861769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544046067/1250000000 : ℝ)|^4175 ≤ (3321391739843/10000000000000 : ℝ)^3151
        have hw : |(544046067/1250000000 : ℝ)|=(544046067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4706610521/10000000000 : ℝ)|^4175 ≤ (18421128867081/50000000000000 : ℝ)^3151
        have hw : |(4706610521/10000000000 : ℝ)|=(4706610521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503110197/1250000000 : ℝ)|^4175 ≤ (29943824861769/100000000000000 : ℝ)^3151
        have hw : |(503110197/1250000000 : ℝ)|=(503110197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1157_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2037/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9137/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8229/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2037/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2037/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2037/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2037/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2037/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2037/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5733/100000 : ℝ) ^ (8349/2048 : ℝ) ≤ (433825561027453/50000000000000000000 : ℝ) := by
    have hpowers : (5733/100000 : ℝ)^8349 ≤ (433825561027453/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5733 : ℕ)^8349*50000000000000000000^2048 ≤ 433825561027453^2048*100000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5733 100000 433825561027453 50000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5733/100000 : ℝ)) (X := (433825561027453/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2037/10000 : ℝ) ^ (8349/2048 : ℝ) ≤ (15240220842641257/10000000000000000000 : ℝ) := by
    have hpowers : (2037/10000 : ℝ)^8349 ≤ (15240220842641257/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2037 : ℕ)^8349*10000000000000000000^2048 ≤ 15240220842641257^2048*10000^8349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2037 10000 15240220842641257 10000000000000000000 8349 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2037/10000 : ℝ)) (X := (15240220842641257/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000433825561027453/25000000000000000000 : ℝ) ≤ (10000042566483707/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (25000433825561027453/25000000000000000000 : ℝ)^2048 ≤ (10000042566483707/10000000000000000 : ℝ)^8349 := by
      have hnat : (25000433825561027453 : ℕ)^2048*10000000000000000^8349 ≤ 10000042566483707^8349*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000433825561027453 25000000000000000000 10000042566483707 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042566483707/10000000000000000 : ℝ)) (X := (25000433825561027453/25000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25038317464887116869/25000000000000000000 : ℝ) ≤ (1000375751932183/1000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (25038317464887116869/25000000000000000000 : ℝ)^2048 ≤ (1000375751932183/1000000000000000 : ℝ)^8349 := by
      have hnat : (25038317464887116869 : ℕ)^2048*1000000000000000^8349 ≤ 1000375751932183^8349*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25038317464887116869 25000000000000000000 1000375751932183 1000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000375751932183/1000000000000000 : ℝ)) (X := (25038317464887116869/25000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5015240220842641257/5000000000000000000 : ℝ) ≤ (10007472472159953/10000000000000000 : ℝ) ^ (8349/2048 : ℝ) := by
    have hpowers : (5015240220842641257/5000000000000000000 : ℝ)^2048 ≤ (10007472472159953/10000000000000000 : ℝ)^8349 := by
      have hnat : (5015240220842641257 : ℕ)^2048*10000000000000000^8349 ≤ 10007472472159953^8349*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5015240220842641257 5000000000000000000 10007472472159953 10000000000000000 2048 8349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007472472159953/10000000000000000 : ℝ)) (X := (5015240220842641257/5000000000000000000 : ℝ)) (by norm_num) 8349 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(433825561027453/50000000000000000000 : ℝ) ≤ ((6968001304589528621/6970000000000000000 : ℝ)+2*(3714952838123/1463700000000000 : ℝ)*(5733/100000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (6968001304589528621/6970000000000000000 : ℝ)+2*(3714952838123/1463700000000000 : ℝ)*(5733/100000 : ℝ)=(10000042566483707/10000000000000000 : ℝ) by norm_num, show 1+2*(433825561027453/50000000000000000000 : ℝ)=(25000433825561027453/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15240220842641257/10000000000000000000 : ℝ)+(433825561027453/50000000000000000000 : ℝ) ≤ ((6968001304589528621/6970000000000000000 : ℝ)+(3714952838123/1463700000000000 : ℝ)*((2037/10000 : ℝ)+(5733/100000 : ℝ)))^(8349/2048 : ℝ) := by
    rw [show (6968001304589528621/6970000000000000000 : ℝ)+(3714952838123/1463700000000000 : ℝ)*((2037/10000 : ℝ)+(5733/100000 : ℝ))=(1000375751932183/1000000000000000 : ℝ) by norm_num, show 1+(15240220842641257/10000000000000000000 : ℝ)+(433825561027453/50000000000000000000 : ℝ)=(25038317464887116869/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15240220842641257/10000000000000000000 : ℝ) ≤ ((6968001304589528621/6970000000000000000 : ℝ)+2*(3714952838123/1463700000000000 : ℝ)*(2037/10000 : ℝ))^(8349/2048 : ℝ) := by
    rw [show (6968001304589528621/6970000000000000000 : ℝ)+2*(3714952838123/1463700000000000 : ℝ)*(2037/10000 : ℝ)=(10007472472159953/10000000000000000 : ℝ) by norm_num, show 1+2*(15240220842641257/10000000000000000000 : ℝ)=(5015240220842641257/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6968001304589528621/6970000000000000000 : ℝ)*(X 1 0+X 2 0)+(3714952838123/1463700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (5733/100000 : ℝ)) (hi := (2037/10000 : ℝ)) (c := (6968001304589528621/6970000000000000000 : ℝ)) (alpha := (3714952838123/1463700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6968001304589528621/6970000000000000000 : ℝ)*(X 0 1+X 2 1)+(3714952838123/1463700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (5733/100000 : ℝ)) (hi := (2037/10000 : ℝ)) (c := (6968001304589528621/6970000000000000000 : ℝ)) (alpha := (3714952838123/1463700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6968001304589528621/6970000000000000000 : ℝ)*(X 0 2+X 1 2)+(3714952838123/1463700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8349/2048 : ℝ)) (lo := (5733/100000 : ℝ)) (hi := (2037/10000 : ℝ)) (c := (6968001304589528621/6970000000000000000 : ℝ)) (alpha := (3714952838123/1463700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53577/250000 : ℝ)*X 0 0+(1376996463/2500000000 : ℝ)*X 0 1+(1032314323/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343306079/2500000000 : ℝ)*X 1 0+(-464615289/2000000000 : ℝ)*X 1 1+(258078703/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343306137/2500000000 : ℝ)*X 2 0+(5161573557/10000000000 : ℝ)*X 2 1+(-290384599/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352171437/10000000000 : ℝ)*X 0 0+(8040241/20000000 : ℝ)*X 0 1+(235566303/500000000 : ℝ)*X 0 2+(4352171437/10000000000 : ℝ)*X 1 0+(8040241/20000000 : ℝ)*X 1 1+(235566303/500000000 : ℝ)*X 1 2+(4352171437/10000000000 : ℝ)*X 2 0+(8040241/20000000 : ℝ)*X 2 1+(235566303/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214317799/1000000000 : ℝ)*X 0 0+(516393607/1000000000 : ℝ)*X 0 1+(5505598343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057048427/2000000000 : ℝ)*X 1 0+(-197905113/1000000000 : ℝ)*X 1 1+(5505598333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057048449/2000000000 : ℝ)*X 2 0+(2752799163/5000000000 : ℝ)*X 2 1+(-494762747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544046067/1250000000 : ℝ)*X 0 0+(4706610521/10000000000 : ℝ)*X 0 1+(503110197/1250000000 : ℝ)*X 0 2+(544046067/1250000000 : ℝ)*X 1 0+(4706610521/10000000000 : ℝ)*X 1 1+(503110197/1250000000 : ℝ)*X 1 2+(544046067/1250000000 : ℝ)*X 2 0+(4706610521/10000000000 : ℝ)*X 2 1+(503110197/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1157_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1935019944781226992936996077/174250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1406801841/100000000000000 : ℝ)*(base19) + (590952309/50000000000000 : ℝ)*(base23) + (474827247/100000000000000 : ℝ)*(upper3) + (93907749/50000000000000 : ℝ)*(upper4) + (12466271/100000000000000 : ℝ)*(upper5) + (1083385842858379/50000000000000 : ℝ)*(major0) + (1083385842858379/50000000000000 : ℝ)*(major1) + (1083385842858379/50000000000000 : ℝ)*(major2) + (1443374767183109/50000000000000 : ℝ)*(sp0) + (1443387313626909/50000000000000 : ℝ)*(sp1) + (2255292853243/78125000000 : ℝ)*(sp2) + (1446754970132913/100000000000000 : ℝ)*(sp3) + (26499689441/100000000000000 : ℝ)*(sp4) + (1499635413/12500000000000 : ℝ)*(sp7) + (1446766967216217/100000000000000 : ℝ)*(f.failure) + (1443388017027829/50000000000000 : ℝ)*(f.sum) + (330751056123259/73185000000000000000000000000 : ℝ)*base65 + (6686348228529827461/7318500000000000000000000000000000 : ℝ)*base68 + (63014469536579327461/7318500000000000000000000000000000 : ℝ)*base70 + (25745402122494672539/7318500000000000000000000000000000 : ℝ)*base71 + (44371403312693/9148125000000000000000000000 : ℝ)*base73 + (76164809550498827461/7318500000000000000000000000000000 : ℝ)*base76 + (29511405722597327461/7318500000000000000000000000000000 : ℝ)*base78 + (8497602254801172539/7318500000000000000000000000000000 : ℝ)*base79 + (72112390212253/36592500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (41898037/10000000000000000000000 : ℝ)*base89 + (41898037/10000000000000000000000 : ℝ)*base91 + (41898037/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3281891947350935782202856623/1219750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (359661099/50000000000000 : ℝ)*(base19) + (53341201/6250000000000 : ℝ)*(base23) + (20330749/100000000000000 : ℝ)*(upper2) + (90062007/100000000000000 : ℝ)*(upper3) + (15783553/25000000000000 : ℝ)*(upper5) + (1098431399036497/50000000000000 : ℝ)*(major0) + (1098431399036497/50000000000000 : ℝ)*(major1) + (1098431399036497/50000000000000 : ℝ)*(major2) + (3347197177/50000000000000 : ℝ)*(sp1) + (4391061009/50000000000000 : ℝ)*(sp2) + (731716628966101/25000000000000 : ℝ)*(sp4) + (731714775536963/25000000000000 : ℝ)*(sp5) + (292685688028317/10000000000000 : ℝ)*(sp6) + (58674359623761/4000000000000 : ℝ)*(sp7) + (58674359623761/4000000000000 : ℝ)*(f.failure) + (731716628966101/25000000000000 : ℝ)*(f.sum) + (35573669941931/36592500000000000000000000000 : ℝ)*base65 + (8628829960222706623/7318500000000000000000000000000000 : ℝ)*base68 + (10605090652337793377/7318500000000000000000000000000000 : ℝ)*base69 + (10558345109465793377/7318500000000000000000000000000000 : ℝ)*base71 + (306344160713/73185000000000000000000000000 : ℝ)*base74 + (11830899999533793377/7318500000000000000000000000000000 : ℝ)*base75 + (24468188975810793377/7318500000000000000000000000000000 : ℝ)*base77 + (27434441456593706623/7318500000000000000000000000000000 : ℝ)*base80 + (6315194529611/36592500000000000000000000000 : ℝ)*base81 + (479821/400000000000000000000 : ℝ)*base89 + (479821/400000000000000000000 : ℝ)*base91 + (479821/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1157_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2037/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8229/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1157_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1157_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8229/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1157_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1157_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1157_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8349/2048 : ℝ) ≤ p) (hpb : p ≤ (4175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149766461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9137/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8229/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1157_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
