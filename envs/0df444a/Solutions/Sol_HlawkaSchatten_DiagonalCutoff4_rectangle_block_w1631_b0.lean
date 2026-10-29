-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1631_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:58.217474+00:00
-- url     : https://prove2.me/submissions/ca256988-3d2b-4d72-8dad-f2a5380e7357

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
theorem support_rectangle_w1631_s0_0 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1526589937/10000000000 : ℝ)*x 0 + (363083719/625000000 : ℝ)*x 1 + (4908347031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1526589937/10000000000 : ℝ)^4843 ≤ (4611279228479/50000000000000 : ℝ)^3819 := by
    have hnat : (1526589937 : ℕ)^4843*50000000000000^3819 ≤ 4611279228479^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526589937 10000000000 4611279228479 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363083719/625000000 : ℝ)^4843 ≤ (50220537122957/100000000000000 : ℝ)^3819 := by
    have hnat : (363083719 : ℕ)^4843*100000000000000^3819 ≤ 50220537122957^3819*625000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363083719 625000000 50220537122957 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4908347031/10000000000 : ℝ)^4843 ≤ (10139226100527/25000000000000 : ℝ)^3819 := by
    have hnat : (4908347031 : ℕ)^4843*25000000000000^3819 ≤ 10139226100527^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908347031 10000000000 10139226100527 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1526589937/10000000000 : ℝ), (363083719/625000000 : ℝ), (4908347031/10000000000 : ℝ)] ![(4611279228479/50000000000000 : ℝ), (50220537122957/100000000000000 : ℝ), (10139226100527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1526589937/10000000000 : ℝ)|^4843 ≤ (4611279228479/50000000000000 : ℝ)^3819
        have hw : |(-1526589937/10000000000 : ℝ)|=(1526589937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(363083719/625000000 : ℝ)|^4843 ≤ (50220537122957/100000000000000 : ℝ)^3819
        have hw : |(363083719/625000000 : ℝ)|=(363083719/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4908347031/10000000000 : ℝ)|^4843 ≤ (10139226100527/25000000000000 : ℝ)^3819
        have hw : |(4908347031/10000000000 : ℝ)|=(4908347031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s0_1 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5445143777/10000000000 : ℝ)*x 0 + (-252893051/1250000000 : ℝ)*x 1 + (2454174309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5445143777/10000000000 : ℝ)^4843 ≤ (23131017991109/50000000000000 : ℝ)^3819 := by
    have hnat : (5445143777 : ℕ)^4843*50000000000000^3819 ≤ 23131017991109^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445143777 10000000000 23131017991109 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252893051/1250000000 : ℝ)^4843 ≤ (3295260742971/25000000000000 : ℝ)^3819 := by
    have hnat : (252893051 : ℕ)^4843*25000000000000^3819 ≤ 3295260742971^3819*1250000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252893051 1250000000 3295260742971 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2454174309/5000000000 : ℝ)^4843 ≤ (20278460515653/50000000000000 : ℝ)^3819 := by
    have hnat : (2454174309 : ℕ)^4843*50000000000000^3819 ≤ 20278460515653^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454174309 5000000000 20278460515653 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5445143777/10000000000 : ℝ), (-252893051/1250000000 : ℝ), (2454174309/5000000000 : ℝ)] ![(23131017991109/50000000000000 : ℝ), (3295260742971/25000000000000 : ℝ), (20278460515653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5445143777/10000000000 : ℝ)|^4843 ≤ (23131017991109/50000000000000 : ℝ)^3819
        have hw : |(5445143777/10000000000 : ℝ)|=(5445143777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-252893051/1250000000 : ℝ)|^4843 ≤ (3295260742971/25000000000000 : ℝ)^3819
        have hw : |(-252893051/1250000000 : ℝ)|=(252893051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2454174309/5000000000 : ℝ)|^4843 ≤ (20278460515653/50000000000000 : ℝ)^3819
        have hw : |(2454174309/5000000000 : ℝ)|=(2454174309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s0_2 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1089028857/2000000000 : ℝ)*x 0 + (4908347483/10000000000 : ℝ)*x 1 + (-404629037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089028857/2000000000 : ℝ)^4843 ≤ (46262041455451/100000000000000 : ℝ)^3819 := by
    have hnat : (1089028857 : ℕ)^4843*100000000000000^3819 ≤ 46262041455451^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089028857 2000000000 46262041455451 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4908347483/10000000000 : ℝ)^4843 ≤ (20278454569169/50000000000000 : ℝ)^3819 := by
    have hnat : (4908347483 : ℕ)^4843*50000000000000^3819 ≤ 20278454569169^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908347483 10000000000 20278454569169 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404629037/2000000000 : ℝ)^4843 ≤ (1647631173937/12500000000000 : ℝ)^3819 := by
    have hnat : (404629037 : ℕ)^4843*12500000000000^3819 ≤ 1647631173937^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404629037 2000000000 1647631173937 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089028857/2000000000 : ℝ), (4908347483/10000000000 : ℝ), (-404629037/2000000000 : ℝ)] ![(46262041455451/100000000000000 : ℝ), (20278454569169/50000000000000 : ℝ), (1647631173937/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089028857/2000000000 : ℝ)|^4843 ≤ (46262041455451/100000000000000 : ℝ)^3819
        have hw : |(1089028857/2000000000 : ℝ)|=(1089028857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4908347483/10000000000 : ℝ)|^4843 ≤ (20278454569169/50000000000000 : ℝ)^3819
        have hw : |(4908347483/10000000000 : ℝ)|=(4908347483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404629037/2000000000 : ℝ)|^4843 ≤ (1647631173937/12500000000000 : ℝ)^3819
        have hw : |(-404629037/2000000000 : ℝ)|=(404629037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s0_3 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4099605743/10000000000 : ℝ)*x 0 + (3078231573/10000000000 : ℝ)*x 1 + (2676811009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4099605743/10000000000 : ℝ)^4843 ≤ (4034739258243/12500000000000 : ℝ)^3819 := by
    have hnat : (4099605743 : ℕ)^4843*12500000000000^3819 ≤ 4034739258243^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4099605743 10000000000 4034739258243 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3078231573/10000000000 : ℝ)^4843 ≤ (11221940773339/50000000000000 : ℝ)^3819 := by
    have hnat : (3078231573 : ℕ)^4843*50000000000000^3819 ≤ 11221940773339^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3078231573 10000000000 11221940773339 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2676811009/5000000000 : ℝ)^4843 ≤ (45278204373817/100000000000000 : ℝ)^3819 := by
    have hnat : (2676811009 : ℕ)^4843*100000000000000^3819 ≤ 45278204373817^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676811009 5000000000 45278204373817 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4099605743/10000000000 : ℝ), (3078231573/10000000000 : ℝ), (2676811009/5000000000 : ℝ)] ![(4034739258243/12500000000000 : ℝ), (11221940773339/50000000000000 : ℝ), (45278204373817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4099605743/10000000000 : ℝ)|^4843 ≤ (4034739258243/12500000000000 : ℝ)^3819
        have hw : |(4099605743/10000000000 : ℝ)|=(4099605743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3078231573/10000000000 : ℝ)|^4843 ≤ (11221940773339/50000000000000 : ℝ)^3819
        have hw : |(3078231573/10000000000 : ℝ)|=(3078231573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2676811009/5000000000 : ℝ)|^4843 ≤ (45278204373817/100000000000000 : ℝ)^3819
        have hw : |(2676811009/5000000000 : ℝ)|=(2676811009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s0_4 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1529112501/10000000000 : ℝ)*x 0 + (154091243/312500000 : ℝ)*x 1 + (2892987469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1529112501/10000000000 : ℝ)^4843 ≤ (1848377694357/20000000000000 : ℝ)^3819 := by
    have hnat : (1529112501 : ℕ)^4843*20000000000000^3819 ≤ 1848377694357^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529112501 10000000000 1848377694357 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154091243/312500000 : ℝ)^4843 ≤ (20396787990291/50000000000000 : ℝ)^3819 := by
    have hnat : (154091243 : ℕ)^4843*50000000000000^3819 ≤ 20396787990291^3819*312500000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154091243 312500000 20396787990291 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2892987469/5000000000 : ℝ)^4843 ≤ (9992907107059/20000000000000 : ℝ)^3819 := by
    have hnat : (2892987469 : ℕ)^4843*20000000000000^3819 ≤ 9992907107059^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2892987469 5000000000 9992907107059 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1529112501/10000000000 : ℝ), (154091243/312500000 : ℝ), (2892987469/5000000000 : ℝ)] ![(1848377694357/20000000000000 : ℝ), (20396787990291/50000000000000 : ℝ), (9992907107059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1529112501/10000000000 : ℝ)|^4843 ≤ (1848377694357/20000000000000 : ℝ)^3819
        have hw : |(-1529112501/10000000000 : ℝ)|=(1529112501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154091243/312500000 : ℝ)|^4843 ≤ (20396787990291/50000000000000 : ℝ)^3819
        have hw : |(154091243/312500000 : ℝ)|=(154091243/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2892987469/5000000000 : ℝ)|^4843 ≤ (9992907107059/20000000000000 : ℝ)^3819
        have hw : |(2892987469/5000000000 : ℝ)|=(2892987469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s0_5 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599577159/5000000000 : ℝ)*x 0 + (-143189889/1250000000 : ℝ)*x 1 + (2892986963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599577159/5000000000 : ℝ)^4843 ≤ (21813979054681/50000000000000 : ℝ)^3819 := by
    have hnat : (2599577159 : ℕ)^4843*50000000000000^3819 ≤ 21813979054681^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599577159 5000000000 21813979054681 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143189889/1250000000 : ℝ)^4843 ≤ (1601879355503/25000000000000 : ℝ)^3819 := by
    have hnat : (143189889 : ℕ)^4843*25000000000000^3819 ≤ 1601879355503^3819*1250000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143189889 1250000000 1601879355503 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2892986963/5000000000 : ℝ)^4843 ≤ (49964524452977/100000000000000 : ℝ)^3819 := by
    have hnat : (2892986963 : ℕ)^4843*100000000000000^3819 ≤ 49964524452977^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2892986963 5000000000 49964524452977 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599577159/5000000000 : ℝ), (-143189889/1250000000 : ℝ), (2892986963/5000000000 : ℝ)] ![(21813979054681/50000000000000 : ℝ), (1601879355503/25000000000000 : ℝ), (49964524452977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599577159/5000000000 : ℝ)|^4843 ≤ (21813979054681/50000000000000 : ℝ)^3819
        have hw : |(2599577159/5000000000 : ℝ)|=(2599577159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-143189889/1250000000 : ℝ)|^4843 ≤ (1601879355503/25000000000000 : ℝ)^3819
        have hw : |(-143189889/1250000000 : ℝ)|=(143189889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2892986963/5000000000 : ℝ)|^4843 ≤ (49964524452977/100000000000000 : ℝ)^3819
        have hw : |(2892986963/5000000000 : ℝ)|=(2892986963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s0_6 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519915173/1000000000 : ℝ)*x 0 + (5785977679/10000000000 : ℝ)*x 1 + (-1145517201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519915173/1000000000 : ℝ)^4843 ≤ (43627930569533/100000000000000 : ℝ)^3819 := by
    have hnat : (519915173 : ℕ)^4843*100000000000000^3819 ≤ 43627930569533^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519915173 1000000000 43627930569533 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5785977679/10000000000 : ℝ)^4843 ≤ (9992913110347/20000000000000 : ℝ)^3819 := by
    have hnat : (5785977679 : ℕ)^4843*20000000000000^3819 ≤ 9992913110347^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5785977679 10000000000 9992913110347 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145517201/10000000000 : ℝ)^4843 ≤ (1601875966649/25000000000000 : ℝ)^3819 := by
    have hnat : (1145517201 : ℕ)^4843*25000000000000^3819 ≤ 1601875966649^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145517201 10000000000 1601875966649 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519915173/1000000000 : ℝ), (5785977679/10000000000 : ℝ), (-1145517201/10000000000 : ℝ)] ![(43627930569533/100000000000000 : ℝ), (9992913110347/20000000000000 : ℝ), (1601875966649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519915173/1000000000 : ℝ)|^4843 ≤ (43627930569533/100000000000000 : ℝ)^3819
        have hw : |(519915173/1000000000 : ℝ)|=(519915173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5785977679/10000000000 : ℝ)|^4843 ≤ (9992913110347/20000000000000 : ℝ)^3819
        have hw : |(5785977679/10000000000 : ℝ)|=(5785977679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1145517201/10000000000 : ℝ)|^4843 ≤ (1601875966649/25000000000000 : ℝ)^3819
        have hw : |(-1145517201/10000000000 : ℝ)|=(1145517201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s0_7 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2052985461/5000000000 : ℝ)*x 0 + (5296616641/10000000000 : ℝ)*x 1 + (3137235317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052985461/5000000000 : ℝ)^4843 ≤ (32341480691507/100000000000000 : ℝ)^3819 := by
    have hnat : (2052985461 : ℕ)^4843*100000000000000^3819 ≤ 32341480691507^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052985461 5000000000 32341480691507 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5296616641/10000000000 : ℝ)^4843 ≤ (44667684105039/100000000000000 : ℝ)^3819 := by
    have hnat : (5296616641 : ℕ)^4843*100000000000000^3819 ≤ 44667684105039^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296616641 10000000000 44667684105039 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3137235317/10000000000 : ℝ)^4843 ≤ (22990835183111/100000000000000 : ℝ)^3819 := by
    have hnat : (3137235317 : ℕ)^4843*100000000000000^3819 ≤ 22990835183111^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137235317 10000000000 22990835183111 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2052985461/5000000000 : ℝ), (5296616641/10000000000 : ℝ), (3137235317/10000000000 : ℝ)] ![(32341480691507/100000000000000 : ℝ), (44667684105039/100000000000000 : ℝ), (22990835183111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2052985461/5000000000 : ℝ)|^4843 ≤ (32341480691507/100000000000000 : ℝ)^3819
        have hw : |(2052985461/5000000000 : ℝ)|=(2052985461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5296616641/10000000000 : ℝ)|^4843 ≤ (44667684105039/100000000000000 : ℝ)^3819
        have hw : |(5296616641/10000000000 : ℝ)|=(5296616641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3137235317/10000000000 : ℝ)|^4843 ≤ (22990835183111/100000000000000 : ℝ)^3819
        have hw : |(3137235317/10000000000 : ℝ)|=(3137235317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1631_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2233/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2971/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4839/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4839 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4839*1^1024 ≤ 0^1024*1^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4839/1024 : ℝ) ≤ (1316740795160465777/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4839 ≤ (1316740795160465777/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4839*100000000000000000000^1024 ≤ 1316740795160465777^1024*5^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1316740795160465777 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1316740795160465777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4839 := by
      have hnat : (1 : ℕ)^1024*1^4839 ≤ 1^4839*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101316740795160465777/100000000000000000000 : ℝ) ≤ (10027720571142799/10000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (101316740795160465777/100000000000000000000 : ℝ)^1024 ≤ (10027720571142799/10000000000000000 : ℝ)^4839 := by
      have hnat : (101316740795160465777 : ℕ)^1024*10000000000000000^4839 ≤ 10027720571142799^4839*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101316740795160465777 100000000000000000000 10027720571142799 10000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027720571142799/10000000000000000 : ℝ)) (X := (101316740795160465777/100000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51316740795160465777/50000000000000000000 : ℝ) ≤ (5027720571142799/5000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (51316740795160465777/50000000000000000000 : ℝ)^1024 ≤ (5027720571142799/5000000000000000 : ℝ)^4839 := by
      have hnat : (51316740795160465777 : ℕ)^1024*5000000000000000^4839 ≤ 5027720571142799^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51316740795160465777 50000000000000000000 5027720571142799 5000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027720571142799/5000000000000000 : ℝ)) (X := (51316740795160465777/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27720571142799/4000000000000000 : ℝ)*(0 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27720571142799/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1316740795160465777/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27720571142799/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4839/1024 : ℝ) := by
    rw [show (1 : ℝ)+(27720571142799/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10027720571142799/10000000000000000 : ℝ) by norm_num, show 1+(1316740795160465777/100000000000000000000 : ℝ)+(0 : ℝ)=(101316740795160465777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1316740795160465777/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27720571142799/4000000000000000 : ℝ)*(2/5 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(27720571142799/4000000000000000 : ℝ)*(2/5 : ℝ)=(5027720571142799/5000000000000000 : ℝ) by norm_num, show 1+2*(1316740795160465777/100000000000000000000 : ℝ)=(51316740795160465777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27720571142799/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27720571142799/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27720571142799/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27720571142799/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27720571142799/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27720571142799/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1526589937/10000000000 : ℝ)*X 0 0+(363083719/625000000 : ℝ)*X 0 1+(4908347031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5445143777/10000000000 : ℝ)*X 1 0+(-252893051/1250000000 : ℝ)*X 1 1+(2454174309/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1089028857/2000000000 : ℝ)*X 2 0+(4908347483/10000000000 : ℝ)*X 2 1+(-404629037/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4099605743/10000000000 : ℝ)*X 0 0+(3078231573/10000000000 : ℝ)*X 0 1+(2676811009/5000000000 : ℝ)*X 0 2+(4099605743/10000000000 : ℝ)*X 1 0+(3078231573/10000000000 : ℝ)*X 1 1+(2676811009/5000000000 : ℝ)*X 1 2+(4099605743/10000000000 : ℝ)*X 2 0+(3078231573/10000000000 : ℝ)*X 2 1+(2676811009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1529112501/10000000000 : ℝ)*X 0 0+(154091243/312500000 : ℝ)*X 0 1+(2892987469/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2599577159/5000000000 : ℝ)*X 1 0+(-143189889/1250000000 : ℝ)*X 1 1+(2892986963/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519915173/1000000000 : ℝ)*X 2 0+(5785977679/10000000000 : ℝ)*X 2 1+(-1145517201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2052985461/5000000000 : ℝ)*X 0 0+(5296616641/10000000000 : ℝ)*X 0 1+(3137235317/10000000000 : ℝ)*X 0 2+(2052985461/5000000000 : ℝ)*X 1 0+(5296616641/10000000000 : ℝ)*X 1 1+(3137235317/10000000000 : ℝ)*X 1 2+(2052985461/5000000000 : ℝ)*X 2 0+(5296616641/10000000000 : ℝ)*X 2 1+(3137235317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1481112729702651201/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (105211/800000000000 : ℝ)*(base16) + (415990569/100000000000000 : ℝ)*(base19) + (583061961/100000000000000 : ℝ)*(base23) + (5485819/20000000000000 : ℝ)*(upper2) + (9100989/6250000000000 : ℝ)*(upper3) + (774690760316469/100000000000000 : ℝ)*(major0) + (774690760316469/100000000000000 : ℝ)*(major1) + (774690760316469/100000000000000 : ℝ)*(major2) + (554945484962361/50000000000000 : ℝ)*(sp0) + (110989322844847/10000000000000 : ℝ)*(sp1) + (277473268632113/25000000000000 : ℝ)*(sp2) + (43948611905941/10000000000000 : ℝ)*(sp3) + (671916423/25000000000000 : ℝ)*(sp4) + (82262113/5000000000000 : ℝ)*(sp7) + (43948776430167/10000000000000 : ℝ)*(f.failure) + (554946828795207/50000000000000 : ℝ)*(f.sum) + (232937198343269/200000000000000000000000000000 : ℝ)*base66 + (311751157543269/400000000000000000000000000000 : ℝ)*base68 + (302979080743269/400000000000000000000000000000 : ℝ)*base70 + (133095614456731/400000000000000000000000000000 : ℝ)*base71 + (303157264456731/200000000000000000000000000000 : ℝ)*base73 + (643813873543269/400000000000000000000000000000 : ℝ)*base76 + (1343714637543269/400000000000000000000000000000 : ℝ)*base78 + (2325951468056731/400000000000000000000000000000 : ℝ)*base79 + (505329794456731/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1283559/250000000000000000000 : ℝ)*base90 + (1283559/250000000000000000000 : ℝ)*base92 + (1283559/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3911257375505132845929/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149217487/25000000000000 : ℝ)*(base19) + (58320787/50000000000000 : ℝ)*(upper2) + (33291907/25000000000000 : ℝ)*(upper3) + (88199349/50000000000000 : ℝ)*(upper4) + (62104829/50000000000000 : ℝ)*(upper5) + (163261125970957/20000000000000 : ℝ)*(major0) + (163261125970957/20000000000000 : ℝ)*(major1) + (163261125970957/20000000000000 : ℝ)*(major2) + (423636619/20000000000000 : ℝ)*(sp2) + (332134633/100000000000000 : ℝ)*(sp3) + (292378766855869/25000000000000 : ℝ)*(sp4) + (1169514470553527/100000000000000 : ℝ)*(sp5) + (1169512949240381/100000000000000 : ℝ)*(sp6) + (463095853632693/100000000000000 : ℝ)*(sp7) + (231548092883663/50000000000000 : ℝ)*(f.failure) + (292378766855869/25000000000000 : ℝ)*(f.sum) + (206580902128643/40000000000000000000000000000 : ℝ)*base65 + (537645890151357/80000000000000000000000000000 : ℝ)*base68 + (598089031351357/80000000000000000000000000000 : ℝ)*base70 + (329005585608643/80000000000000000000000000000 : ℝ)*base71 + (194428182231357/40000000000000000000000000000 : ℝ)*base74 + (230671567528643/80000000000000000000000000000 : ℝ)*base75 + (441609743911357/80000000000000000000000000000 : ℝ)*base78 + (231469426791357/80000000000000000000000000000 : ℝ)*base80 + (36121103071357/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (8175649/1250000000000000000000 : ℝ)*base89 + (8175649/1250000000000000000000 : ℝ)*base91 + (8175649/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1631_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2233/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2971/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1631_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1631_s1_0 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-164054367/1000000000 : ℝ)*x 0 + (110226163/200000000 : ℝ)*x 1 + (102649811/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164054367/1000000000 : ℝ)^4843 ≤ (5052078700967/50000000000000 : ℝ)^3819 := by
    have hnat : (164054367 : ℕ)^4843*50000000000000^3819 ≤ 5052078700967^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164054367 1000000000 5052078700967 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110226163/200000000 : ℝ)^4843 ≤ (46976054101057/100000000000000 : ℝ)^3819 := by
    have hnat : (110226163 : ℕ)^4843*100000000000000^3819 ≤ 46976054101057^3819*200000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110226163 200000000 46976054101057 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102649811/200000000 : ℝ)^4843 ≤ (42919788479699/100000000000000 : ℝ)^3819 := by
    have hnat : (102649811 : ℕ)^4843*100000000000000^3819 ≤ 42919788479699^3819*200000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102649811 200000000 42919788479699 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-164054367/1000000000 : ℝ), (110226163/200000000 : ℝ), (102649811/200000000 : ℝ)] ![(5052078700967/50000000000000 : ℝ), (46976054101057/100000000000000 : ℝ), (42919788479699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-164054367/1000000000 : ℝ)|^4843 ≤ (5052078700967/50000000000000 : ℝ)^3819
        have hw : |(-164054367/1000000000 : ℝ)|=(164054367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110226163/200000000 : ℝ)|^4843 ≤ (46976054101057/100000000000000 : ℝ)^3819
        have hw : |(110226163/200000000 : ℝ)|=(110226163/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102649811/200000000 : ℝ)|^4843 ≤ (42919788479699/100000000000000 : ℝ)^3819
        have hw : |(102649811/200000000 : ℝ)|=(102649811/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s1_1 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341467493/2500000000 : ℝ)*x 0 + (-1838004029/10000000000 : ℝ)*x 1 + (2566245161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341467493/2500000000 : ℝ)^4843 ≤ (45409606670981/100000000000000 : ℝ)^3819 := by
    have hnat : (1341467493 : ℕ)^4843*100000000000000^3819 ≤ 45409606670981^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341467493 2500000000 45409606670981 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1838004029/10000000000 : ℝ)^4843 ≤ (5835303625811/50000000000000 : ℝ)^3819 := by
    have hnat : (1838004029 : ℕ)^4843*50000000000000^3819 ≤ 5835303625811^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838004029 10000000000 5835303625811 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566245161/5000000000 : ℝ)^4843 ≤ (858395721237/2000000000000 : ℝ)^3819 := by
    have hnat : (2566245161 : ℕ)^4843*2000000000000^3819 ≤ 858395721237^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566245161 5000000000 858395721237 2000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341467493/2500000000 : ℝ), (-1838004029/10000000000 : ℝ), (2566245161/5000000000 : ℝ)] ![(45409606670981/100000000000000 : ℝ), (5835303625811/50000000000000 : ℝ), (858395721237/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341467493/2500000000 : ℝ)|^4843 ≤ (45409606670981/100000000000000 : ℝ)^3819
        have hw : |(1341467493/2500000000 : ℝ)|=(1341467493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1838004029/10000000000 : ℝ)|^4843 ≤ (5835303625811/50000000000000 : ℝ)^3819
        have hw : |(-1838004029/10000000000 : ℝ)|=(1838004029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566245161/5000000000 : ℝ)|^4843 ≤ (858395721237/2000000000000 : ℝ)^3819
        have hw : |(2566245161/5000000000 : ℝ)|=(2566245161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s1_2 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073174149/2000000000 : ℝ)*x 0 + (8211983/16000000 : ℝ)*x 1 + (-919002123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073174149/2000000000 : ℝ)^4843 ≤ (2270480748333/5000000000000 : ℝ)^3819 := by
    have hnat : (1073174149 : ℕ)^4843*5000000000000^3819 ≤ 2270480748333^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073174149 2000000000 2270480748333 5000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8211983/16000000 : ℝ)^4843 ≤ (1341243000603/3125000000000 : ℝ)^3819 := by
    have hnat : (8211983 : ℕ)^4843*3125000000000^3819 ≤ 1341243000603^3819*16000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8211983 16000000 1341243000603 3125000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919002123/5000000000 : ℝ)^4843 ≤ (11670608998939/100000000000000 : ℝ)^3819 := by
    have hnat : (919002123 : ℕ)^4843*100000000000000^3819 ≤ 11670608998939^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919002123 5000000000 11670608998939 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073174149/2000000000 : ℝ), (8211983/16000000 : ℝ), (-919002123/5000000000 : ℝ)] ![(2270480748333/5000000000000 : ℝ), (1341243000603/3125000000000 : ℝ), (11670608998939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073174149/2000000000 : ℝ)|^4843 ≤ (2270480748333/5000000000000 : ℝ)^3819
        have hw : |(1073174149/2000000000 : ℝ)|=(1073174149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8211983/16000000 : ℝ)|^4843 ≤ (1341243000603/3125000000000 : ℝ)^3819
        have hw : |(8211983/16000000 : ℝ)|=(8211983/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-919002123/5000000000 : ℝ)|^4843 ≤ (11670608998939/100000000000000 : ℝ)^3819
        have hw : |(-919002123/5000000000 : ℝ)|=(919002123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s1_3 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186524521/10000000000 : ℝ)*x 0 + (23303227/62500000 : ℝ)*x 1 + (4685193933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186524521/10000000000 : ℝ)^4843 ≤ (16574106235853/50000000000000 : ℝ)^3819 := by
    have hnat : (4186524521 : ℕ)^4843*50000000000000^3819 ≤ 16574106235853^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186524521 10000000000 16574106235853 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23303227/62500000 : ℝ)^4843 ≤ (14309376797899/50000000000000 : ℝ)^3819 := by
    have hnat : (23303227 : ℕ)^4843*50000000000000^3819 ≤ 14309376797899^3819*62500000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23303227 62500000 14309376797899 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4685193933/10000000000 : ℝ)^4843 ≤ (4779129239433/12500000000000 : ℝ)^3819 := by
    have hnat : (4685193933 : ℕ)^4843*12500000000000^3819 ≤ 4779129239433^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4685193933 10000000000 4779129239433 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186524521/10000000000 : ℝ), (23303227/62500000 : ℝ), (4685193933/10000000000 : ℝ)] ![(16574106235853/50000000000000 : ℝ), (14309376797899/50000000000000 : ℝ), (4779129239433/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186524521/10000000000 : ℝ)|^4843 ≤ (16574106235853/50000000000000 : ℝ)^3819
        have hw : |(4186524521/10000000000 : ℝ)|=(4186524521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(23303227/62500000 : ℝ)|^4843 ≤ (14309376797899/50000000000000 : ℝ)^3819
        have hw : |(23303227/62500000 : ℝ)|=(23303227/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4685193933/10000000000 : ℝ)|^4843 ≤ (4779129239433/12500000000000 : ℝ)^3819
        have hw : |(4685193933/10000000000 : ℝ)|=(4685193933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s1_4 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1640727999/10000000000 : ℝ)*x 0 + (5136457467/10000000000 : ℝ)*x 1 + (2753641133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1640727999/10000000000 : ℝ)^4843 ≤ (5052798559789/50000000000000 : ℝ)^3819 := by
    have hnat : (1640727999 : ℕ)^4843*50000000000000^3819 ≤ 5052798559789^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640727999 10000000000 5052798559789 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136457467/10000000000 : ℝ)^4843 ≤ (8592372079901/20000000000000 : ℝ)^3819 := by
    have hnat : (5136457467 : ℕ)^4843*20000000000000^3819 ≤ 8592372079901^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136457467 10000000000 8592372079901 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2753641133/5000000000 : ℝ)^4843 ≤ (46932542469677/100000000000000 : ℝ)^3819 := by
    have hnat : (2753641133 : ℕ)^4843*100000000000000^3819 ≤ 46932542469677^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753641133 5000000000 46932542469677 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1640727999/10000000000 : ℝ), (5136457467/10000000000 : ℝ), (2753641133/5000000000 : ℝ)] ![(5052798559789/50000000000000 : ℝ), (8592372079901/20000000000000 : ℝ), (46932542469677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1640727999/10000000000 : ℝ)|^4843 ≤ (5052798559789/50000000000000 : ℝ)^3819
        have hw : |(-1640727999/10000000000 : ℝ)|=(1640727999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136457467/10000000000 : ℝ)|^4843 ≤ (8592372079901/20000000000000 : ℝ)^3819
        have hw : |(5136457467/10000000000 : ℝ)|=(5136457467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2753641133/5000000000 : ℝ)|^4843 ≤ (46932542469677/100000000000000 : ℝ)^3819
        have hw : |(2753641133/5000000000 : ℝ)|=(2753641133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s1_5 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632401043/5000000000 : ℝ)*x 0 + (-146321123/1000000000 : ℝ)*x 1 + (2753641313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632401043/5000000000 : ℝ)^4843 ≤ (44327718348221/100000000000000 : ℝ)^3819 := by
    have hnat : (2632401043 : ℕ)^4843*100000000000000^3819 ≤ 44327718348221^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632401043 5000000000 44327718348221 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146321123/1000000000 : ℝ)^4843 ≤ (2184933820101/25000000000000 : ℝ)^3819 := by
    have hnat : (146321123 : ℕ)^4843*25000000000000^3819 ≤ 2184933820101^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146321123 1000000000 2184933820101 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2753641313/5000000000 : ℝ)^4843 ≤ (9386509272033/20000000000000 : ℝ)^3819 := by
    have hnat : (2753641313 : ℕ)^4843*20000000000000^3819 ≤ 9386509272033^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753641313 5000000000 9386509272033 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632401043/5000000000 : ℝ), (-146321123/1000000000 : ℝ), (2753641313/5000000000 : ℝ)] ![(44327718348221/100000000000000 : ℝ), (2184933820101/25000000000000 : ℝ), (9386509272033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632401043/5000000000 : ℝ)|^4843 ≤ (44327718348221/100000000000000 : ℝ)^3819
        have hw : |(2632401043/5000000000 : ℝ)|=(2632401043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-146321123/1000000000 : ℝ)|^4843 ≤ (2184933820101/25000000000000 : ℝ)^3819
        have hw : |(-146321123/1000000000 : ℝ)|=(146321123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2753641313/5000000000 : ℝ)|^4843 ≤ (9386509272033/20000000000000 : ℝ)^3819
        have hw : |(2753641313/5000000000 : ℝ)|=(2753641313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s1_6 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658100177/1250000000 : ℝ)*x 0 + (550728287/1000000000 : ℝ)*x 1 + (-731605913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658100177/1250000000 : ℝ)^4843 ≤ (11081927798621/25000000000000 : ℝ)^3819 := by
    have hnat : (658100177 : ℕ)^4843*25000000000000^3819 ≤ 11081927798621^3819*1250000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658100177 1250000000 11081927798621 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550728287/1000000000 : ℝ)^4843 ≤ (46932548997051/100000000000000 : ℝ)^3819 := by
    have hnat : (550728287 : ℕ)^4843*100000000000000^3819 ≤ 46932548997051^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550728287 1000000000 46932548997051 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731605913/5000000000 : ℝ)^4843 ≤ (2184934948707/25000000000000 : ℝ)^3819 := by
    have hnat : (731605913 : ℕ)^4843*25000000000000^3819 ≤ 2184934948707^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731605913 5000000000 2184934948707 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658100177/1250000000 : ℝ), (550728287/1000000000 : ℝ), (-731605913/5000000000 : ℝ)] ![(11081927798621/25000000000000 : ℝ), (46932548997051/100000000000000 : ℝ), (2184934948707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658100177/1250000000 : ℝ)|^4843 ≤ (11081927798621/25000000000000 : ℝ)^3819
        have hw : |(658100177/1250000000 : ℝ)|=(658100177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550728287/1000000000 : ℝ)|^4843 ≤ (46932548997051/100000000000000 : ℝ)^3819
        have hw : |(550728287/1000000000 : ℝ)|=(550728287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-731605913/5000000000 : ℝ)|^4843 ≤ (2184934948707/25000000000000 : ℝ)^3819
        have hw : |(-731605913/5000000000 : ℝ)|=(731605913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s1_7 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186987071/10000000000 : ℝ)*x 0 + (935035309/2000000000 : ℝ)*x 1 + (747736487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186987071/10000000000 : ℝ)^4843 ≤ (16576428472143/50000000000000 : ℝ)^3819 := by
    have hnat : (4186987071 : ℕ)^4843*50000000000000^3819 ≤ 16576428472143^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186987071 10000000000 16576428472143 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935035309/2000000000 : ℝ)^4843 ≤ (19064699520703/50000000000000 : ℝ)^3819 := by
    have hnat : (935035309 : ℕ)^4843*50000000000000^3819 ≤ 19064699520703^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935035309 2000000000 19064699520703 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (747736487/2000000000 : ℝ)^4843 ≤ (14358872001993/50000000000000 : ℝ)^3819 := by
    have hnat : (747736487 : ℕ)^4843*50000000000000^3819 ≤ 14358872001993^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747736487 2000000000 14358872001993 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186987071/10000000000 : ℝ), (935035309/2000000000 : ℝ), (747736487/2000000000 : ℝ)] ![(16576428472143/50000000000000 : ℝ), (19064699520703/50000000000000 : ℝ), (14358872001993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186987071/10000000000 : ℝ)|^4843 ≤ (16576428472143/50000000000000 : ℝ)^3819
        have hw : |(4186987071/10000000000 : ℝ)|=(4186987071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(935035309/2000000000 : ℝ)|^4843 ≤ (19064699520703/50000000000000 : ℝ)^3819
        have hw : |(935035309/2000000000 : ℝ)|=(935035309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(747736487/2000000000 : ℝ)|^4843 ≤ (14358872001993/50000000000000 : ℝ)^3819
        have hw : |(747736487/2000000000 : ℝ)|=(747736487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1631_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2971/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9481/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (219/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2971/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2233/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2971/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2233/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2971/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2233/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2971/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2233/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2971/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2233/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2971/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2233/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2233/50000 : ℝ) ^ (4839/1024 : ℝ) ≤ (41694126793711/100000000000000000000 : ℝ) := by
    have hpowers : (2233/50000 : ℝ)^4839 ≤ (41694126793711/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2233 : ℕ)^4839*100000000000000000000^1024 ≤ 41694126793711^1024*50000^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2233 50000 41694126793711 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2233/50000 : ℝ)) (X := (41694126793711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2971/12500 : ℝ) ^ (4839/1024 : ℝ) ≤ (112512192818183399/100000000000000000000 : ℝ) := by
    have hpowers : (2971/12500 : ℝ)^4839 ≤ (112512192818183399/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2971 : ℕ)^4839*100000000000000000000^1024 ≤ 112512192818183399^1024*12500^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2971 12500 112512192818183399 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2971/12500 : ℝ)) (X := (112512192818183399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000041694126793711/50000000000000000000 : ℝ) ≤ (5000000882305679/5000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50000041694126793711/50000000000000000000 : ℝ)^1024 ≤ (5000000882305679/5000000000000000 : ℝ)^4839 := by
      have hnat : (50000041694126793711 : ℕ)^1024*5000000000000000^4839 ≤ 5000000882305679^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000041694126793711 50000000000000000000 5000000882305679 5000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000882305679/5000000000000000 : ℝ)) (X := (50000041694126793711/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10011255388694497711/10000000000000000000 : ℝ) ≤ (2500595185359309/2500000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (10011255388694497711/10000000000000000000 : ℝ)^1024 ≤ (2500595185359309/2500000000000000 : ℝ)^4839 := by
      have hnat : (10011255388694497711 : ℕ)^1024*2500000000000000^4839 ≤ 2500595185359309^4839*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011255388694497711 10000000000000000000 2500595185359309 2500000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500595185359309/2500000000000000 : ℝ)) (X := (10011255388694497711/10000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50112512192818183399/50000000000000000000 : ℝ) ≤ (5002379859131557/5000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50112512192818183399/50000000000000000000 : ℝ)^1024 ≤ (5002379859131557/5000000000000000 : ℝ)^4839 := by
      have hnat : (50112512192818183399 : ℕ)^1024*5000000000000000^4839 ≤ 5002379859131557^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50112512192818183399 50000000000000000000 5002379859131557 5000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002379859131557/5000000000000000 : ℝ)) (X := (50112512192818183399/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(41694126793711/100000000000000000000 : ℝ) ≤ ((9649939251975984491/9651000000000000000 : ℝ)+2*(1189488412939/965100000000000 : ℝ)*(2233/50000 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (9649939251975984491/9651000000000000000 : ℝ)+2*(1189488412939/965100000000000 : ℝ)*(2233/50000 : ℝ)=(5000000882305679/5000000000000000 : ℝ) by norm_num, show 1+2*(41694126793711/100000000000000000000 : ℝ)=(50000041694126793711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(112512192818183399/100000000000000000000 : ℝ)+(41694126793711/100000000000000000000 : ℝ) ≤ ((9649939251975984491/9651000000000000000 : ℝ)+(1189488412939/965100000000000 : ℝ)*((2971/12500 : ℝ)+(2233/50000 : ℝ)))^(4839/1024 : ℝ) := by
    rw [show (9649939251975984491/9651000000000000000 : ℝ)+(1189488412939/965100000000000 : ℝ)*((2971/12500 : ℝ)+(2233/50000 : ℝ))=(2500595185359309/2500000000000000 : ℝ) by norm_num, show 1+(112512192818183399/100000000000000000000 : ℝ)+(41694126793711/100000000000000000000 : ℝ)=(10011255388694497711/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(112512192818183399/100000000000000000000 : ℝ) ≤ ((9649939251975984491/9651000000000000000 : ℝ)+2*(1189488412939/965100000000000 : ℝ)*(2971/12500 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (9649939251975984491/9651000000000000000 : ℝ)+2*(1189488412939/965100000000000 : ℝ)*(2971/12500 : ℝ)=(5002379859131557/5000000000000000 : ℝ) by norm_num, show 1+2*(112512192818183399/100000000000000000000 : ℝ)=(50112512192818183399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9649939251975984491/9651000000000000000 : ℝ)*(X 1 0+X 2 0)+(1189488412939/965100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (2233/50000 : ℝ)) (hi := (2971/12500 : ℝ)) (c := (9649939251975984491/9651000000000000000 : ℝ)) (alpha := (1189488412939/965100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9649939251975984491/9651000000000000000 : ℝ)*(X 0 1+X 2 1)+(1189488412939/965100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (2233/50000 : ℝ)) (hi := (2971/12500 : ℝ)) (c := (9649939251975984491/9651000000000000000 : ℝ)) (alpha := (1189488412939/965100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9649939251975984491/9651000000000000000 : ℝ)*(X 0 2+X 1 2)+(1189488412939/965100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (2233/50000 : ℝ)) (hi := (2971/12500 : ℝ)) (c := (9649939251975984491/9651000000000000000 : ℝ)) (alpha := (1189488412939/965100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-164054367/1000000000 : ℝ)*X 0 0+(110226163/200000000 : ℝ)*X 0 1+(102649811/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1341467493/2500000000 : ℝ)*X 1 0+(-1838004029/10000000000 : ℝ)*X 1 1+(2566245161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073174149/2000000000 : ℝ)*X 2 0+(8211983/16000000 : ℝ)*X 2 1+(-919002123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4186524521/10000000000 : ℝ)*X 0 0+(23303227/62500000 : ℝ)*X 0 1+(4685193933/10000000000 : ℝ)*X 0 2+(4186524521/10000000000 : ℝ)*X 1 0+(23303227/62500000 : ℝ)*X 1 1+(4685193933/10000000000 : ℝ)*X 1 2+(4186524521/10000000000 : ℝ)*X 2 0+(23303227/62500000 : ℝ)*X 2 1+(4685193933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1640727999/10000000000 : ℝ)*X 0 0+(5136457467/10000000000 : ℝ)*X 0 1+(2753641133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632401043/5000000000 : ℝ)*X 1 0+(-146321123/1000000000 : ℝ)*X 1 1+(2753641313/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((658100177/1250000000 : ℝ)*X 2 0+(550728287/1000000000 : ℝ)*X 2 1+(-731605913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4186987071/10000000000 : ℝ)*X 0 0+(935035309/2000000000 : ℝ)*X 0 1+(747736487/2000000000 : ℝ)*X 0 2+(4186987071/10000000000 : ℝ)*X 1 0+(935035309/2000000000 : ℝ)*X 1 1+(747736487/2000000000 : ℝ)*X 1 2+(4186987071/10000000000 : ℝ)*X 2 0+(935035309/2000000000 : ℝ)*X 2 1+(747736487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214575013023425050232262747/20106250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (490299307/100000000000000 : ℝ)*(base1) + (63595663/4000000000000 : ℝ)*(base19) + (985089069/50000000000000 : ℝ)*(base23) + (26579713/12500000000000 : ℝ)*(upper3) + (72034383/50000000000000 : ℝ)*(upper5) + (460637179859583/25000000000000 : ℝ)*(major0) + (460637179859583/25000000000000 : ℝ)*(major1) + (460637179859583/25000000000000 : ℝ)*(major2) + (2639799482782101/100000000000000 : ℝ)*(sp0) + (2639804057229607/100000000000000 : ℝ)*(sp1) + (659950919235761/25000000000000 : ℝ)*(sp2) + (1045287111592797/100000000000000 : ℝ)*(sp3) + (1663659597/25000000000000 : ℝ)*(sp4) + (3834128193/100000000000000 : ℝ)*(sp7) + (522645718010149/50000000000000 : ℝ)*(f.failure) + (1319902823560591/50000000000000 : ℝ)*(f.sum) + (12554921346507/8042500000000000000000000000 : ℝ)*base66 + (988025548530690751/80425000000000000000000000000000 : ℝ)*base67 + (216354369474915751/80425000000000000000000000000000 : ℝ)*base69 + (125400861317834249/80425000000000000000000000000000 : ℝ)*base72 + (31330572608023/8042500000000000000000000000 : ℝ)*base73 + (208915805249115751/80425000000000000000000000000000 : ℝ)*base75 + (427908117222365751/80425000000000000000000000000000 : ℝ)*base77 + (210533657470240751/80425000000000000000000000000000 : ℝ)*base79 + (10271893159163/2010625000000000000000000000 : ℝ)*base82 + (8335627/1250000000000000000000 : ℝ)*base89 + (8335627/1250000000000000000000 : ℝ)*base91 + (8335627/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21921433348793634463279/2010625000000000000000000000 : ℝ) := by norm_num
    linear_combination (209320513/10000000000000 : ℝ)*(base19) + (446157719/25000000000000 : ℝ)*(base23) + (967111/4000000000000 : ℝ)*(upper2) + (215062323/50000000000000 : ℝ)*(upper3) + (114970393/100000000000000 : ℝ)*(upper5) + (235281142871491/12500000000000 : ℝ)*(major0) + (235281142871491/12500000000000 : ℝ)*(major1) + (235281142871491/12500000000000 : ℝ)*(major2) + (2025701577/12500000000000 : ℝ)*(sp1) + (1951981973/12500000000000 : ℝ)*(sp2) + (269668414432597/10000000000000 : ℝ)*(sp4) + (2696665845508223/100000000000000 : ℝ)*(sp5) + (2696666743839309/100000000000000 : ℝ)*(sp6) + (533906889095681/50000000000000 : ℝ)*(sp7) + (533906889095681/50000000000000 : ℝ)*(f.failure) + (269668414432597/10000000000000 : ℝ)*(f.sum) + (32716772897621/6031875000000000000000000000 : ℝ)*base66 + (68460079636987973/40212500000000000000000000000000 : ℝ)*base68 + (148895221631612973/40212500000000000000000000000000 : ℝ)*base70 + (72385072133212027/40212500000000000000000000000000 : ℝ)*base71 + (942569420029/376992187500000000000000000 : ℝ)*base73 + (202365472483262027/40212500000000000000000000000000 : ℝ)*base75 + (30759214024262973/40212500000000000000000000000000 : ℝ)*base78 + (208519042572012027/40212500000000000000000000000000 : ℝ)*base79 + (31582092679867/12063750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (372463/1250000000000000000000 : ℝ)*base89 + (372463/1250000000000000000000 : ℝ)*base91 + (372463/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1631_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2971/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2233/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9481/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (219/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1631_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1631_s2_0 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-412954393/2500000000 : ℝ)*x 0 + (1364537429/2500000000 : ℝ)*x 1 + (2589118953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412954393/2500000000 : ℝ)^4843 ≤ (1019229285511/10000000000000 : ℝ)^3819 := by
    have hnat : (412954393 : ℕ)^4843*10000000000000^3819 ≤ 1019229285511^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412954393 2500000000 1019229285511 10000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364537429/2500000000 : ℝ)^4843 ≤ (46402207856933/100000000000000 : ℝ)^3819 := by
    have hnat : (1364537429 : ℕ)^4843*100000000000000^3819 ≤ 46402207856933^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364537429 2500000000 46402207856933 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589118953/5000000000 : ℝ)^4843 ≤ (10851374820291/25000000000000 : ℝ)^3819 := by
    have hnat : (2589118953 : ℕ)^4843*25000000000000^3819 ≤ 10851374820291^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589118953 5000000000 10851374820291 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412954393/2500000000 : ℝ), (1364537429/2500000000 : ℝ), (2589118953/5000000000 : ℝ)] ![(1019229285511/10000000000000 : ℝ), (46402207856933/100000000000000 : ℝ), (10851374820291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412954393/2500000000 : ℝ)|^4843 ≤ (1019229285511/10000000000000 : ℝ)^3819
        have hw : |(-412954393/2500000000 : ℝ)|=(412954393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364537429/2500000000 : ℝ)|^4843 ≤ (46402207856933/100000000000000 : ℝ)^3819
        have hw : |(1364537429/2500000000 : ℝ)|=(1364537429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589118953/5000000000 : ℝ)|^4843 ≤ (10851374820291/25000000000000 : ℝ)^3819
        have hw : |(2589118953/5000000000 : ℝ)|=(2589118953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s2_1 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351897389/10000000000 : ℝ)*x 0 + (-898085327/5000000000 : ℝ)*x 1 + (517823793/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351897389/10000000000 : ℝ)^4843 ≤ (45259708143407/100000000000000 : ℝ)^3819 := by
    have hnat : (5351897389 : ℕ)^4843*100000000000000^3819 ≤ 45259708143407^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351897389 10000000000 45259708143407 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898085327/5000000000 : ℝ)^4843 ≤ (70842451867/625000000000 : ℝ)^3819 := by
    have hnat : (898085327 : ℕ)^4843*625000000000^3819 ≤ 70842451867^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898085327 5000000000 70842451867 625000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517823793/1000000000 : ℝ)^4843 ≤ (43405499536281/100000000000000 : ℝ)^3819 := by
    have hnat : (517823793 : ℕ)^4843*100000000000000^3819 ≤ 43405499536281^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517823793 1000000000 43405499536281 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351897389/10000000000 : ℝ), (-898085327/5000000000 : ℝ), (517823793/1000000000 : ℝ)] ![(45259708143407/100000000000000 : ℝ), (70842451867/625000000000 : ℝ), (43405499536281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351897389/10000000000 : ℝ)|^4843 ≤ (45259708143407/100000000000000 : ℝ)^3819
        have hw : |(5351897389/10000000000 : ℝ)|=(5351897389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-898085327/5000000000 : ℝ)|^4843 ≤ (70842451867/625000000000 : ℝ)^3819
        have hw : |(-898085327/5000000000 : ℝ)|=(898085327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517823793/1000000000 : ℝ)|^4843 ≤ (43405499536281/100000000000000 : ℝ)^3819
        have hw : |(517823793/1000000000 : ℝ)|=(517823793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s2_2 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070379481/2000000000 : ℝ)*x 0 + (323639867/625000000 : ℝ)*x 1 + (-179617071/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070379481/2000000000 : ℝ)^4843 ≤ (9051941662999/20000000000000 : ℝ)^3819 := by
    have hnat : (1070379481 : ℕ)^4843*20000000000000^3819 ≤ 9051941662999^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070379481 2000000000 9051941662999 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323639867/625000000 : ℝ)^4843 ≤ (43405498919749/100000000000000 : ℝ)^3819 := by
    have hnat : (323639867 : ℕ)^4843*100000000000000^3819 ≤ 43405498919749^3819*625000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323639867 625000000 43405498919749 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179617071/1000000000 : ℝ)^4843 ≤ (2266958549373/20000000000000 : ℝ)^3819 := by
    have hnat : (179617071 : ℕ)^4843*20000000000000^3819 ≤ 2266958549373^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179617071 1000000000 2266958549373 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070379481/2000000000 : ℝ), (323639867/625000000 : ℝ), (-179617071/1000000000 : ℝ)] ![(9051941662999/20000000000000 : ℝ), (43405498919749/100000000000000 : ℝ), (2266958549373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070379481/2000000000 : ℝ)|^4843 ≤ (9051941662999/20000000000000 : ℝ)^3819
        have hw : |(1070379481/2000000000 : ℝ)|=(1070379481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323639867/625000000 : ℝ)|^4843 ≤ (43405498919749/100000000000000 : ℝ)^3819
        have hw : |(323639867/625000000 : ℝ)|=(323639867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-179617071/1000000000 : ℝ)|^4843 ≤ (2266958549373/20000000000000 : ℝ)^3819
        have hw : |(-179617071/1000000000 : ℝ)|=(179617071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s2_3 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4194889311/10000000000 : ℝ)*x 0 + (3852545777/10000000000 : ℝ)*x 1 + (4559442283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194889311/10000000000 : ℝ)^4843 ≤ (16616112358263/50000000000000 : ℝ)^3819 := by
    have hnat : (4194889311 : ℕ)^4843*50000000000000^3819 ≤ 16616112358263^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194889311 10000000000 16616112358263 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3852545777/10000000000 : ℝ)^4843 ≤ (29831364377961/100000000000000 : ℝ)^3819 := by
    have hnat : (3852545777 : ℕ)^4843*100000000000000^3819 ≤ 29831364377961^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3852545777 10000000000 29831364377961 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4559442283/10000000000 : ℝ)^4843 ≤ (36936410891677/100000000000000 : ℝ)^3819 := by
    have hnat : (4559442283 : ℕ)^4843*100000000000000^3819 ≤ 36936410891677^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4559442283 10000000000 36936410891677 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194889311/10000000000 : ℝ), (3852545777/10000000000 : ℝ), (4559442283/10000000000 : ℝ)] ![(16616112358263/50000000000000 : ℝ), (29831364377961/100000000000000 : ℝ), (36936410891677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194889311/10000000000 : ℝ)|^4843 ≤ (16616112358263/50000000000000 : ℝ)^3819
        have hw : |(4194889311/10000000000 : ℝ)|=(4194889311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3852545777/10000000000 : ℝ)|^4843 ≤ (29831364377961/100000000000000 : ℝ)^3819
        have hw : |(3852545777/10000000000 : ℝ)|=(3852545777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4559442283/10000000000 : ℝ)|^4843 ≤ (36936410891677/100000000000000 : ℝ)^3819
        have hw : |(4559442283/10000000000 : ℝ)|=(4559442283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s2_4 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1651891427/10000000000 : ℝ)*x 0 + (518041067/1000000000 : ℝ)*x 1 + (5455953563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1651891427/10000000000 : ℝ)^4843 ≤ (1019287076101/10000000000000 : ℝ)^3819 := by
    have hnat : (1651891427 : ℕ)^4843*10000000000000^3819 ≤ 1019287076101^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651891427 10000000000 1019287076101 10000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518041067/1000000000 : ℝ)^4843 ≤ (4342859675861/10000000000000 : ℝ)^3819 := by
    have hnat : (518041067 : ℕ)^4843*10000000000000^3819 ≤ 4342859675861^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518041067 1000000000 4342859675861 10000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455953563/10000000000 : ℝ)^4843 ≤ (90583071221/195312500000 : ℝ)^3819 := by
    have hnat : (5455953563 : ℕ)^4843*195312500000^3819 ≤ 90583071221^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455953563 10000000000 90583071221 195312500000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1651891427/10000000000 : ℝ), (518041067/1000000000 : ℝ), (5455953563/10000000000 : ℝ)] ![(1019287076101/10000000000000 : ℝ), (4342859675861/10000000000000 : ℝ), (90583071221/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1651891427/10000000000 : ℝ)|^4843 ≤ (1019287076101/10000000000000 : ℝ)^3819
        have hw : |(-1651891427/10000000000 : ℝ)|=(1651891427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518041067/1000000000 : ℝ)|^4843 ≤ (4342859675861/10000000000000 : ℝ)^3819
        have hw : |(518041067/1000000000 : ℝ)|=(518041067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455953563/10000000000 : ℝ)|^4843 ≤ (90583071221/195312500000 : ℝ)^3819
        have hw : |(5455953563/10000000000 : ℝ)|=(5455953563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s2_5 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638649221/5000000000 : ℝ)*x 0 + (-1518454897/10000000000 : ℝ)*x 1 + (2727976833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638649221/5000000000 : ℝ)^4843 ≤ (44461187108017/100000000000000 : ℝ)^3819 := by
    have hnat : (2638649221 : ℕ)^4843*100000000000000^3819 ≤ 44461187108017^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638649221 5000000000 44461187108017 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518454897/10000000000 : ℝ)^4843 ≤ (458013964909/5000000000000 : ℝ)^3819 := by
    have hnat : (1518454897 : ℕ)^4843*5000000000000^3819 ≤ 458013964909^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518454897 10000000000 458013964909 5000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727976833/5000000000 : ℝ)^4843 ≤ (46378533575473/100000000000000 : ℝ)^3819 := by
    have hnat : (2727976833 : ℕ)^4843*100000000000000^3819 ≤ 46378533575473^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727976833 5000000000 46378533575473 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638649221/5000000000 : ℝ), (-1518454897/10000000000 : ℝ), (2727976833/5000000000 : ℝ)] ![(44461187108017/100000000000000 : ℝ), (458013964909/5000000000000 : ℝ), (46378533575473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638649221/5000000000 : ℝ)|^4843 ≤ (44461187108017/100000000000000 : ℝ)^3819
        have hw : |(2638649221/5000000000 : ℝ)|=(2638649221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1518454897/10000000000 : ℝ)|^4843 ≤ (458013964909/5000000000000 : ℝ)^3819
        have hw : |(-1518454897/10000000000 : ℝ)|=(1518454897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727976833/5000000000 : ℝ)|^4843 ≤ (46378533575473/100000000000000 : ℝ)^3819
        have hw : |(2727976833/5000000000 : ℝ)|=(2727976833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s2_6 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527729937/1000000000 : ℝ)*x 0 + (5455952581/10000000000 : ℝ)*x 1 + (-1518455131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527729937/1000000000 : ℝ)^4843 ≤ (44461197022777/100000000000000 : ℝ)^3819 := by
    have hnat : (527729937 : ℕ)^4843*100000000000000^3819 ≤ 44461197022777^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527729937 1000000000 44461197022777 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455952581/10000000000 : ℝ)^4843 ≤ (23189260939689/50000000000000 : ℝ)^3819 := by
    have hnat : (5455952581 : ℕ)^4843*50000000000000^3819 ≤ 23189260939689^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455952581 10000000000 23189260939689 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518455131/10000000000 : ℝ)^4843 ≤ (4580140544161/50000000000000 : ℝ)^3819 := by
    have hnat : (1518455131 : ℕ)^4843*50000000000000^3819 ≤ 4580140544161^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518455131 10000000000 4580140544161 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527729937/1000000000 : ℝ), (5455952581/10000000000 : ℝ), (-1518455131/10000000000 : ℝ)] ![(44461197022777/100000000000000 : ℝ), (23189260939689/50000000000000 : ℝ), (4580140544161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527729937/1000000000 : ℝ)|^4843 ≤ (44461197022777/100000000000000 : ℝ)^3819
        have hw : |(527729937/1000000000 : ℝ)|=(527729937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455952581/10000000000 : ℝ)|^4843 ≤ (23189260939689/50000000000000 : ℝ)^3819
        have hw : |(5455952581/10000000000 : ℝ)|=(5455952581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1518455131/10000000000 : ℝ)|^4843 ≤ (4580140544161/50000000000000 : ℝ)^3819
        have hw : |(-1518455131/10000000000 : ℝ)|=(1518455131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s2_7 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839015297/2000000000 : ℝ)*x 0 + (4553956849/10000000000 : ℝ)*x 1 + (241130699/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839015297/2000000000 : ℝ)^4843 ≤ (8308526280861/25000000000000 : ℝ)^3819 := by
    have hnat : (839015297 : ℕ)^4843*25000000000000^3819 ≤ 8308526280861^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839015297 2000000000 8308526280861 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4553956849/10000000000 : ℝ)^4843 ≤ (18440033379403/50000000000000 : ℝ)^3819 := by
    have hnat : (4553956849 : ℕ)^4843*50000000000000^3819 ≤ 18440033379403^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553956849 10000000000 18440033379403 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241130699/625000000 : ℝ)^4843 ≤ (14942914049989/50000000000000 : ℝ)^3819 := by
    have hnat : (241130699 : ℕ)^4843*50000000000000^3819 ≤ 14942914049989^3819*625000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241130699 625000000 14942914049989 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839015297/2000000000 : ℝ), (4553956849/10000000000 : ℝ), (241130699/625000000 : ℝ)] ![(8308526280861/25000000000000 : ℝ), (18440033379403/50000000000000 : ℝ), (14942914049989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839015297/2000000000 : ℝ)|^4843 ≤ (8308526280861/25000000000000 : ℝ)^3819
        have hw : |(839015297/2000000000 : ℝ)|=(839015297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4553956849/10000000000 : ℝ)|^4843 ≤ (18440033379403/50000000000000 : ℝ)^3819
        have hw : |(4553956849/10000000000 : ℝ)|=(4553956849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241130699/625000000 : ℝ)|^4843 ≤ (14942914049989/50000000000000 : ℝ)^3819
        have hw : |(241130699/625000000 : ℝ)|=(241130699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1631_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (219/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10469/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16411/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (219/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (219/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (219/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (219/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (219/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (219/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9481/100000 : ℝ) ^ (4839/1024 : ℝ) ≤ (1462299538895227/100000000000000000000 : ℝ) := by
    have hpowers : (9481/100000 : ℝ)^4839 ≤ (1462299538895227/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9481 : ℕ)^4839*100000000000000000000^1024 ≤ 1462299538895227^1024*100000^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9481 100000 1462299538895227 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9481/100000 : ℝ)) (X := (1462299538895227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (219/1250 : ℝ) ^ (4839/1024 : ℝ) ≤ (26622901749304923/100000000000000000000 : ℝ) := by
    have hpowers : (219/1250 : ℝ)^4839 ≤ (26622901749304923/100000000000000000000 : ℝ)^1024 := by
      have hnat : (219 : ℕ)^4839*100000000000000000000^1024 ≤ 26622901749304923^1024*1250^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        219 1250 26622901749304923 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (219/1250 : ℝ)) (X := (26622901749304923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001462299538895227/50000000000000000000 : ℝ) ≤ (10000061887888627/10000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50001462299538895227/50000000000000000000 : ℝ)^1024 ≤ (10000061887888627/10000000000000000 : ℝ)^4839 := by
      have hnat : (50001462299538895227 : ℕ)^1024*10000000000000000^4839 ≤ 10000061887888627^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001462299538895227 50000000000000000000 10000061887888627 10000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061887888627/10000000000000000 : ℝ)) (X := (50001462299538895227/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000561704025764003/2000000000000000000 : ℝ) ≤ (10000594256307477/10000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (2000561704025764003/2000000000000000000 : ℝ)^1024 ≤ (10000594256307477/10000000000000000 : ℝ)^4839 := by
      have hnat : (2000561704025764003 : ℕ)^1024*10000000000000000^4839 ≤ 10000594256307477^4839*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000561704025764003 2000000000000000000 10000594256307477 10000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000594256307477/10000000000000000 : ℝ)) (X := (2000561704025764003/2000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026622901749304923/50000000000000000000 : ℝ) ≤ (10001126624726327/10000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50026622901749304923/50000000000000000000 : ℝ)^1024 ≤ (10001126624726327/10000000000000000 : ℝ)^4839 := by
      have hnat : (50026622901749304923 : ℕ)^1024*10000000000000000^4839 ≤ 10001126624726327^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026622901749304923 50000000000000000000 10001126624726327 10000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001126624726327/10000000000000000 : ℝ)) (X := (50026622901749304923/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1462299538895227/100000000000000000000 : ℝ) ≤ ((80380402746778438753/80390000000000000000 : ℝ)+2*(10647368377/16078000000000 : ℝ)*(9481/100000 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (80380402746778438753/80390000000000000000 : ℝ)+2*(10647368377/16078000000000 : ℝ)*(9481/100000 : ℝ)=(10000061887888627/10000000000000000 : ℝ) by norm_num, show 1+2*(1462299538895227/100000000000000000000 : ℝ)=(50001462299538895227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26622901749304923/100000000000000000000 : ℝ)+(1462299538895227/100000000000000000000 : ℝ) ≤ ((80380402746778438753/80390000000000000000 : ℝ)+(10647368377/16078000000000 : ℝ)*((219/1250 : ℝ)+(9481/100000 : ℝ)))^(4839/1024 : ℝ) := by
    rw [show (80380402746778438753/80390000000000000000 : ℝ)+(10647368377/16078000000000 : ℝ)*((219/1250 : ℝ)+(9481/100000 : ℝ))=(10000594256307477/10000000000000000 : ℝ) by norm_num, show 1+(26622901749304923/100000000000000000000 : ℝ)+(1462299538895227/100000000000000000000 : ℝ)=(2000561704025764003/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26622901749304923/100000000000000000000 : ℝ) ≤ ((80380402746778438753/80390000000000000000 : ℝ)+2*(10647368377/16078000000000 : ℝ)*(219/1250 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (80380402746778438753/80390000000000000000 : ℝ)+2*(10647368377/16078000000000 : ℝ)*(219/1250 : ℝ)=(10001126624726327/10000000000000000 : ℝ) by norm_num, show 1+2*(26622901749304923/100000000000000000000 : ℝ)=(50026622901749304923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (80380402746778438753/80390000000000000000 : ℝ)*(X 1 0+X 2 0)+(10647368377/16078000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (9481/100000 : ℝ)) (hi := (219/1250 : ℝ)) (c := (80380402746778438753/80390000000000000000 : ℝ)) (alpha := (10647368377/16078000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (80380402746778438753/80390000000000000000 : ℝ)*(X 0 1+X 2 1)+(10647368377/16078000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (9481/100000 : ℝ)) (hi := (219/1250 : ℝ)) (c := (80380402746778438753/80390000000000000000 : ℝ)) (alpha := (10647368377/16078000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (80380402746778438753/80390000000000000000 : ℝ)*(X 0 2+X 1 2)+(10647368377/16078000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (9481/100000 : ℝ)) (hi := (219/1250 : ℝ)) (c := (80380402746778438753/80390000000000000000 : ℝ)) (alpha := (10647368377/16078000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-412954393/2500000000 : ℝ)*X 0 0+(1364537429/2500000000 : ℝ)*X 0 1+(2589118953/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351897389/10000000000 : ℝ)*X 1 0+(-898085327/5000000000 : ℝ)*X 1 1+(517823793/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070379481/2000000000 : ℝ)*X 2 0+(323639867/625000000 : ℝ)*X 2 1+(-179617071/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4194889311/10000000000 : ℝ)*X 0 0+(3852545777/10000000000 : ℝ)*X 0 1+(4559442283/10000000000 : ℝ)*X 0 2+(4194889311/10000000000 : ℝ)*X 1 0+(3852545777/10000000000 : ℝ)*X 1 1+(4559442283/10000000000 : ℝ)*X 1 2+(4194889311/10000000000 : ℝ)*X 2 0+(3852545777/10000000000 : ℝ)*X 2 1+(4559442283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1651891427/10000000000 : ℝ)*X 0 0+(518041067/1000000000 : ℝ)*X 0 1+(5455953563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638649221/5000000000 : ℝ)*X 1 0+(-1518454897/10000000000 : ℝ)*X 1 1+(2727976833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527729937/1000000000 : ℝ)*X 2 0+(5455952581/10000000000 : ℝ)*X 2 1+(-1518455131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((839015297/2000000000 : ℝ)*X 0 0+(4553956849/10000000000 : ℝ)*X 0 1+(241130699/625000000 : ℝ)*X 0 2+(839015297/2000000000 : ℝ)*X 1 0+(4553956849/10000000000 : ℝ)*X 1 1+(241130699/625000000 : ℝ)*X 1 2+(839015297/2000000000 : ℝ)*X 2 0+(4553956849/10000000000 : ℝ)*X 2 1+(241130699/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39226265829357534881953802757/4019500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379419693/25000000000000 : ℝ)*(base19) + (88771713/6250000000000 : ℝ)*(base23) + (5780689/10000000000000 : ℝ)*(lower2) + (259585951/100000000000000 : ℝ)*(upper3) + (69378281/50000000000000 : ℝ)*(upper5) + (2493619537503223/100000000000000 : ℝ)*(major0) + (2493619537503223/100000000000000 : ℝ)*(major1) + (311702442187903/12500000000000 : ℝ)*(major2) + (446571592463859/12500000000000 : ℝ)*(sp0) + (3572588533870561/100000000000000 : ℝ)*(sp1) + (142903545248077/4000000000000 : ℝ)*(sp2) + (176830102128507/12500000000000 : ℝ)*(sp3) + (17311838461/100000000000000 : ℝ)*(sp4) + (7881129341/100000000000000 : ℝ)*(sp7) + (1414648698157397/100000000000000 : ℝ)*(f.failure) + (3572590051549333/100000000000000 : ℝ)*(f.sum) + (6367487608993/1607800000000000000000000000 : ℝ)*base65 + (89962562275591399081/8039000000000000000000000000000000 : ℝ)*base68 + (217441269341745041/1004875000000000000000000000000000 : ℝ)*base70 + (42148228519284399081/8039000000000000000000000000000000 : ℝ)*base72 + (15280921169679/4019500000000000000000000000 : ℝ)*base74 + (3363452744652629959/1004875000000000000000000000000000 : ℝ)*base75 + (30482032534386600919/8039000000000000000000000000000000 : ℝ)*base77 + (12074578024218399081/8039000000000000000000000000000000 : ℝ)*base80 + (505042610367/502437500000000000000000000 : ℝ)*base81 + (22136731/2500000000000000000000 : ℝ)*base89 + (22136731/2500000000000000000000 : ℝ)*base91 + (2863269/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (351301857953676332571/80390000000000000000000000 : ℝ) := by norm_num
    linear_combination (9146767/2500000000000 : ℝ)*(base19) + (1248348473/100000000000000 : ℝ)*(base23) + (59819/5000000000000 : ℝ)*(upper3) + (1534861/1250000000000 : ℝ)*(lower4) + (39580188665083/1562500000000 : ℝ)*(major0) + (39580188665083/1562500000000 : ℝ)*(major1) + (39580188665083/1562500000000 : ℝ)*(major2) + (7289385549/100000000000000 : ℝ)*(sp1) + (4055698933/50000000000000 : ℝ)*(sp2) + (2520284377/100000000000000 : ℝ)*(sp3) + (3629199552513243/100000000000000 : ℝ)*(sp4) + (1814595948628507/50000000000000 : ℝ)*(sp5) + (453648774095863/12500000000000 : ℝ)*(sp6) + (359265482666837/25000000000000 : ℝ)*(sp7) + (57482578038069/4000000000000 : ℝ)*(f.failure) + (3629199552513243/100000000000000 : ℝ)*(f.sum) + (3714662882933/4019500000000000000000000000 : ℝ)*base65 + (1712384602822937/62804687500000000000000000000000 : ℝ)*base67 + (185355110627151001/125609375000000000000000000000000 : ℝ)*base70 + (95909120005411499/125609375000000000000000000000000 : ℝ)*base71 + (6301634854937/8039000000000000000000000000 : ℝ)*base73 + (151619910904111969/31402343750000000000000000000000 : ℝ)*base76 + (14488510543686203/15701171875000000000000000000000 : ℝ)*base77 + (20494679437414711/7850585937500000000000000000000 : ℝ)*base80 + (36305050620119/8039000000000000000000000000 : ℝ)*base81 + (46213/100000000000000000000 : ℝ)*base90 + (46213/100000000000000000000 : ℝ)*base92 + (46213/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1631_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (219/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10469/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16411/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1631_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1631_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10469/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16411/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1631_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1631_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1631_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10469/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16411/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1631_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
