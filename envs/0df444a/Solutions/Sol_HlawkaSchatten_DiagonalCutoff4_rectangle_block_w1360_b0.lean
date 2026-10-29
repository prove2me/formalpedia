-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:35.971902+00:00
-- url     : https://prove2.me/submissions/5815b626-0664-4b53-b76d-23a8240c9707

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
theorem support_rectangle_w1360_s0_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-224819107/1250000000 : ℝ)*x 0 + (748647347/1250000000 : ℝ)*x 1 + (4815185473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224819107/1250000000 : ℝ)^135 ≤ (10554630554549/100000000000000 : ℝ)^103 := by
    have hnat : (224819107 : ℕ)^135*100000000000000^103 ≤ 10554630554549^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224819107 1250000000 10554630554549 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (748647347/1250000000 : ℝ)^135 ≤ (51073994918909/100000000000000 : ℝ)^103 := by
    have hnat : (748647347 : ℕ)^135*100000000000000^103 ≤ 51073994918909^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748647347 1250000000 51073994918909 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4815185473/10000000000 : ℝ)^135 ≤ (19185687254417/50000000000000 : ℝ)^103 := by
    have hnat : (4815185473 : ℕ)^135*50000000000000^103 ≤ 19185687254417^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815185473 10000000000 19185687254417 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224819107/1250000000 : ℝ), (748647347/1250000000 : ℝ), (4815185473/10000000000 : ℝ)] ![(10554630554549/100000000000000 : ℝ), (51073994918909/100000000000000 : ℝ), (19185687254417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224819107/1250000000 : ℝ)|^135 ≤ (10554630554549/100000000000000 : ℝ)^103
        have hw : |(-224819107/1250000000 : ℝ)|=(224819107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(748647347/1250000000 : ℝ)|^135 ≤ (51073994918909/100000000000000 : ℝ)^103
        have hw : |(748647347/1250000000 : ℝ)|=(748647347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4815185473/10000000000 : ℝ)|^135 ≤ (19185687254417/50000000000000 : ℝ)^103
        have hw : |(4815185473/10000000000 : ℝ)|=(4815185473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s0_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1099959579/2000000000 : ℝ)*x 0 + (-98599083/400000000 : ℝ)*x 1 + (2407592987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099959579/2000000000 : ℝ)^135 ≤ (1826996623979/4000000000000 : ℝ)^103 := by
    have hnat : (1099959579 : ℕ)^135*4000000000000^103 ≤ 1826996623979^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099959579 2000000000 1826996623979 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98599083/400000000 : ℝ)^135 ≤ (15953704650479/100000000000000 : ℝ)^103 := by
    have hnat : (98599083 : ℕ)^135*100000000000000^103 ≤ 15953704650479^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98599083 400000000 15953704650479 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2407592987/5000000000 : ℝ)^135 ≤ (38371379741567/100000000000000 : ℝ)^103 := by
    have hnat : (2407592987 : ℕ)^135*100000000000000^103 ≤ 38371379741567^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2407592987 5000000000 38371379741567 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099959579/2000000000 : ℝ), (-98599083/400000000 : ℝ), (2407592987/5000000000 : ℝ)] ![(1826996623979/4000000000000 : ℝ), (15953704650479/100000000000000 : ℝ), (38371379741567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099959579/2000000000 : ℝ)|^135 ≤ (1826996623979/4000000000000 : ℝ)^103
        have hw : |(1099959579/2000000000 : ℝ)|=(1099959579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98599083/400000000 : ℝ)|^135 ≤ (15953704650479/100000000000000 : ℝ)^103
        have hw : |(-98599083/400000000 : ℝ)|=(98599083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2407592987/5000000000 : ℝ)|^135 ≤ (38371379741567/100000000000000 : ℝ)^103
        have hw : |(2407592987/5000000000 : ℝ)|=(2407592987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s0_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2749898879/5000000000 : ℝ)*x 0 + (4815185477/10000000000 : ℝ)*x 1 + (-1232488931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2749898879/5000000000 : ℝ)^135 ≤ (45674914108233/100000000000000 : ℝ)^103 := by
    have hnat : (2749898879 : ℕ)^135*100000000000000^103 ≤ 45674914108233^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749898879 5000000000 45674914108233 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815185477/10000000000 : ℝ)^135 ≤ (9592843637653/25000000000000 : ℝ)^103 := by
    have hnat : (4815185477 : ℕ)^135*25000000000000^103 ≤ 9592843637653^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815185477 10000000000 9592843637653 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1232488931/5000000000 : ℝ)^135 ≤ (3190742265307/20000000000000 : ℝ)^103 := by
    have hnat : (1232488931 : ℕ)^135*20000000000000^103 ≤ 3190742265307^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232488931 5000000000 3190742265307 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2749898879/5000000000 : ℝ), (4815185477/10000000000 : ℝ), (-1232488931/5000000000 : ℝ)] ![(45674914108233/100000000000000 : ℝ), (9592843637653/25000000000000 : ℝ), (3190742265307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2749898879/5000000000 : ℝ)|^135 ≤ (45674914108233/100000000000000 : ℝ)^103
        have hw : |(2749898879/5000000000 : ℝ)|=(2749898879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815185477/10000000000 : ℝ)|^135 ≤ (9592843637653/25000000000000 : ℝ)^103
        have hw : |(4815185477/10000000000 : ℝ)|=(4815185477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1232488931/5000000000 : ℝ)|^135 ≤ (3190742265307/20000000000000 : ℝ)^103
        have hw : |(-1232488931/5000000000 : ℝ)|=(1232488931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s0_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4176064633/10000000000 : ℝ)*x 0 + (24263447/78125000 : ℝ)*x 1 + (5581398077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176064633/10000000000 : ℝ)^135 ≤ (7959528184063/25000000000000 : ℝ)^103 := by
    have hnat : (4176064633 : ℕ)^135*25000000000000^103 ≤ 7959528184063^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176064633 10000000000 7959528184063 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24263447/78125000 : ℝ)^135 ≤ (21596715234281/100000000000000 : ℝ)^103 := by
    have hnat : (24263447 : ℕ)^135*100000000000000^103 ≤ 21596715234281^103*78125000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24263447 78125000 21596715234281 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5581398077/10000000000 : ℝ)^135 ≤ (46565172004761/100000000000000 : ℝ)^103 := by
    have hnat : (5581398077 : ℕ)^135*100000000000000^103 ≤ 46565172004761^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5581398077 10000000000 46565172004761 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176064633/10000000000 : ℝ), (24263447/78125000 : ℝ), (5581398077/10000000000 : ℝ)] ![(7959528184063/25000000000000 : ℝ), (21596715234281/100000000000000 : ℝ), (46565172004761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176064633/10000000000 : ℝ)|^135 ≤ (7959528184063/25000000000000 : ℝ)^103
        have hw : |(4176064633/10000000000 : ℝ)|=(4176064633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(24263447/78125000 : ℝ)|^135 ≤ (21596715234281/100000000000000 : ℝ)^103
        have hw : |(24263447/78125000 : ℝ)|=(24263447/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5581398077/10000000000 : ℝ)|^135 ≤ (46565172004761/100000000000000 : ℝ)^103
        have hw : |(5581398077/10000000000 : ℝ)|=(5581398077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s0_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-901457957/5000000000 : ℝ)*x 0 + (242268399/500000000 : ℝ)*x 1 + (1489479491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901457957/5000000000 : ℝ)^135 ≤ (10588202066127/100000000000000 : ℝ)^103 := by
    have hnat : (901457957 : ℕ)^135*100000000000000^103 ≤ 10588202066127^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901457957 5000000000 10588202066127 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242268399/500000000 : ℝ)^135 ≤ (38686924556403/100000000000000 : ℝ)^103 := by
    have hnat : (242268399 : ℕ)^135*100000000000000^103 ≤ 38686924556403^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242268399 500000000 38686924556403 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489479491/2500000000 : ℝ)^135 ≤ (50724873369383/100000000000000 : ℝ)^103 := by
    have hnat : (1489479491 : ℕ)^135*100000000000000^103 ≤ 50724873369383^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489479491 2500000000 50724873369383 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901457957/5000000000 : ℝ), (242268399/500000000 : ℝ), (1489479491/2500000000 : ℝ)] ![(10588202066127/100000000000000 : ℝ), (38686924556403/100000000000000 : ℝ), (50724873369383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901457957/5000000000 : ℝ)|^135 ≤ (10588202066127/100000000000000 : ℝ)^103
        have hw : |(-901457957/5000000000 : ℝ)|=(901457957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242268399/500000000 : ℝ)|^135 ≤ (38686924556403/100000000000000 : ℝ)^103
        have hw : |(242268399/500000000 : ℝ)|=(242268399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1489479491/2500000000 : ℝ)|^135 ≤ (50724873369383/100000000000000 : ℝ)^103
        have hw : |(1489479491/2500000000 : ℝ)|=(1489479491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s0_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5179735751/10000000000 : ℝ)*x 0 + (-661123429/5000000000 : ℝ)*x 1 + (59579173/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179735751/10000000000 : ℝ)^135 ≤ (8444594450323/20000000000000 : ℝ)^103 := by
    have hnat : (5179735751 : ℕ)^135*20000000000000^103 ≤ 8444594450323^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179735751 10000000000 8444594450323 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (661123429/5000000000 : ℝ)^135 ≤ (7052161769331/100000000000000 : ℝ)^103 := by
    have hnat : (661123429 : ℕ)^135*100000000000000^103 ≤ 7052161769331^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661123429 5000000000 7052161769331 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59579173/100000000 : ℝ)^135 ≤ (25362432979923/50000000000000 : ℝ)^103 := by
    have hnat : (59579173 : ℕ)^135*50000000000000^103 ≤ 25362432979923^103*100000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59579173 100000000 25362432979923 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179735751/10000000000 : ℝ), (-661123429/5000000000 : ℝ), (59579173/100000000 : ℝ)] ![(8444594450323/20000000000000 : ℝ), (7052161769331/100000000000000 : ℝ), (25362432979923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179735751/10000000000 : ℝ)|^135 ≤ (8444594450323/20000000000000 : ℝ)^103
        have hw : |(5179735751/10000000000 : ℝ)|=(5179735751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-661123429/5000000000 : ℝ)|^135 ≤ (7052161769331/100000000000000 : ℝ)^103
        have hw : |(-661123429/5000000000 : ℝ)|=(661123429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59579173/100000000 : ℝ)|^135 ≤ (25362432979923/50000000000000 : ℝ)^103
        have hw : |(59579173/100000000 : ℝ)|=(59579173/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s0_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2589867763/5000000000 : ℝ)*x 0 + (5957918187/10000000000 : ℝ)*x 1 + (-1322245787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589867763/5000000000 : ℝ)^135 ≤ (42222969847693/100000000000000 : ℝ)^103 := by
    have hnat : (2589867763 : ℕ)^135*100000000000000^103 ≤ 42222969847693^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589867763 5000000000 42222969847693 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5957918187/10000000000 : ℝ)^135 ≤ (50724875857827/100000000000000 : ℝ)^103 := by
    have hnat : (5957918187 : ℕ)^135*100000000000000^103 ≤ 50724875857827^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5957918187 10000000000 50724875857827 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1322245787/10000000000 : ℝ)^135 ≤ (7052154282541/100000000000000 : ℝ)^103 := by
    have hnat : (1322245787 : ℕ)^135*100000000000000^103 ≤ 7052154282541^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322245787 10000000000 7052154282541 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589867763/5000000000 : ℝ), (5957918187/10000000000 : ℝ), (-1322245787/10000000000 : ℝ)] ![(42222969847693/100000000000000 : ℝ), (50724875857827/100000000000000 : ℝ), (7052154282541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589867763/5000000000 : ℝ)|^135 ≤ (42222969847693/100000000000000 : ℝ)^103
        have hw : |(2589867763/5000000000 : ℝ)|=(2589867763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5957918187/10000000000 : ℝ)|^135 ≤ (50724875857827/100000000000000 : ℝ)^103
        have hw : |(5957918187/10000000000 : ℝ)|=(5957918187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1322245787/10000000000 : ℝ)|^135 ≤ (7052154282541/100000000000000 : ℝ)^103
        have hw : |(-1322245787/10000000000 : ℝ)|=(1322245787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s0_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4185261123/10000000000 : ℝ)*x 0 + (5517751897/10000000000 : ℝ)*x 1 + (1585821517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185261123/10000000000 : ℝ)^135 ≤ (31930040610531/100000000000000 : ℝ)^103 := by
    have hnat : (4185261123 : ℕ)^135*100000000000000^103 ≤ 31930040610531^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185261123 10000000000 31930040610531 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517751897/10000000000 : ℝ)^135 ≤ (22935221774963/50000000000000 : ℝ)^103 := by
    have hnat : (5517751897 : ℕ)^135*50000000000000^103 ≤ 22935221774963^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517751897 10000000000 22935221774963 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585821517/5000000000 : ℝ)^135 ≤ (22199515822323/100000000000000 : ℝ)^103 := by
    have hnat : (1585821517 : ℕ)^135*100000000000000^103 ≤ 22199515822323^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585821517 5000000000 22199515822323 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185261123/10000000000 : ℝ), (5517751897/10000000000 : ℝ), (1585821517/5000000000 : ℝ)] ![(31930040610531/100000000000000 : ℝ), (22935221774963/50000000000000 : ℝ), (22199515822323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185261123/10000000000 : ℝ)|^135 ≤ (31930040610531/100000000000000 : ℝ)^103
        have hw : |(4185261123/10000000000 : ℝ)|=(4185261123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517751897/10000000000 : ℝ)|^135 ≤ (22935221774963/50000000000000 : ℝ)^103
        have hw : |(5517751897/10000000000 : ℝ)|=(5517751897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1585821517/5000000000 : ℝ)|^135 ≤ (22199515822323/100000000000000 : ℝ)^103
        have hw : |(1585821517/5000000000 : ℝ)|=(1585821517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (387/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13371/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4319/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4319 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4319*1^1024 ≤ 0^1024*1^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4319/1024 : ℝ) ≤ (2096907155581303681/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4319 ≤ (2096907155581303681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4319*100000000000000000000^1024 ≤ 2096907155581303681^1024*5^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2096907155581303681 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2096907155581303681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4319 := by
      have hnat : (1 : ℕ)^1024*1^4319 ≤ 1^4319*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102096907155581303681/100000000000000000000 : ℝ) ≤ (401972925578447/400000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (102096907155581303681/100000000000000000000 : ℝ)^1024 ≤ (401972925578447/400000000000000 : ℝ)^4319 := by
      have hnat : (102096907155581303681 : ℕ)^1024*400000000000000^4319 ≤ 401972925578447^4319*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102096907155581303681 100000000000000000000 401972925578447 400000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401972925578447/400000000000000 : ℝ)) (X := (102096907155581303681/100000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52096907155581303681/50000000000000000000 : ℝ) ≤ (201972925578447/200000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (52096907155581303681/50000000000000000000 : ℝ)^1024 ≤ (201972925578447/200000000000000 : ℝ)^4319 := by
      have hnat : (52096907155581303681 : ℕ)^1024*200000000000000^4319 ≤ 201972925578447^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52096907155581303681 50000000000000000000 201972925578447 200000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201972925578447/200000000000000 : ℝ)) (X := (52096907155581303681/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1972925578447/160000000000000 : ℝ)*(0 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1972925578447/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2096907155581303681/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1972925578447/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1972925578447/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(401972925578447/400000000000000 : ℝ) by norm_num, show 1+(2096907155581303681/100000000000000000000 : ℝ)+(0 : ℝ)=(102096907155581303681/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2096907155581303681/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1972925578447/160000000000000 : ℝ)*(2/5 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1972925578447/160000000000000 : ℝ)*(2/5 : ℝ)=(201972925578447/200000000000000 : ℝ) by norm_num, show 1+2*(2096907155581303681/100000000000000000000 : ℝ)=(52096907155581303681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1972925578447/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1972925578447/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1972925578447/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1972925578447/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1972925578447/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1972925578447/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-224819107/1250000000 : ℝ)*X 0 0+(748647347/1250000000 : ℝ)*X 0 1+(4815185473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1099959579/2000000000 : ℝ)*X 1 0+(-98599083/400000000 : ℝ)*X 1 1+(2407592987/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2749898879/5000000000 : ℝ)*X 2 0+(4815185477/10000000000 : ℝ)*X 2 1+(-1232488931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4176064633/10000000000 : ℝ)*X 0 0+(24263447/78125000 : ℝ)*X 0 1+(5581398077/10000000000 : ℝ)*X 0 2+(4176064633/10000000000 : ℝ)*X 1 0+(24263447/78125000 : ℝ)*X 1 1+(5581398077/10000000000 : ℝ)*X 1 2+(4176064633/10000000000 : ℝ)*X 2 0+(24263447/78125000 : ℝ)*X 2 1+(5581398077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-901457957/5000000000 : ℝ)*X 0 0+(242268399/500000000 : ℝ)*X 0 1+(1489479491/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5179735751/10000000000 : ℝ)*X 1 0+(-661123429/5000000000 : ℝ)*X 1 1+(59579173/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589867763/5000000000 : ℝ)*X 2 0+(5957918187/10000000000 : ℝ)*X 2 1+(-1322245787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4185261123/10000000000 : ℝ)*X 0 0+(5517751897/10000000000 : ℝ)*X 0 1+(1585821517/5000000000 : ℝ)*X 0 2+(4185261123/10000000000 : ℝ)*X 1 0+(5517751897/10000000000 : ℝ)*X 1 1+(1585821517/5000000000 : ℝ)*X 1 2+(4185261123/10000000000 : ℝ)*X 2 0+(5517751897/10000000000 : ℝ)*X 2 1+(1585821517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8056401418405245324477/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45826647/25000000000000 : ℝ)*(base1) + (1877472149/100000000000000 : ℝ)*(base19) + (1856253717/100000000000000 : ℝ)*(base23) + (303999673/100000000000000 : ℝ)*(upper3) + (18932191/20000000000000 : ℝ)*(upper5) + (78483824179497/12500000000000 : ℝ)*(major0) + (78483824179497/12500000000000 : ℝ)*(major1) + (78483824179497/12500000000000 : ℝ)*(major2) + (851800117722013/100000000000000 : ℝ)*(sp0) + (851803516179389/100000000000000 : ℝ)*(sp1) + (42590176869891/5000000000000 : ℝ)*(sp2) + (403932282608717/100000000000000 : ℝ)*(sp3) + (5459236113/100000000000000 : ℝ)*(sp4) + (3058758389/100000000000000 : ℝ)*(sp7) + (201967762336847/50000000000000 : ℝ)*(f.failure) + (851805393651537/100000000000000 : ℝ)*(f.sum) + (1697287203159/1000000000000000000000000000 : ℝ)*base65 + (14236740764841/2000000000000000000000000000 : ℝ)*base68 + (3192718530841/2000000000000000000000000000 : ℝ)*base70 + (5711323224841/2000000000000000000000000000 : ℝ)*base72 + (1346464128841/1000000000000000000000000000 : ℝ)*base74 + (6733796140841/2000000000000000000000000000 : ℝ)*base76 + (762326034841/2000000000000000000000000000 : ℝ)*base78 + (5127254611159/2000000000000000000000000000 : ℝ)*base79 + (1382793906159/1000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (352787/62500000000000000000 : ℝ)*base90 + (352787/62500000000000000000 : ℝ)*base92 + (352787/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40403368626714560046459/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4628721/1000000000000 : ℝ)*(base19) + (829484157/100000000000000 : ℝ)*(base23) + (390397573/100000000000000 : ℝ)*(base39) + (529797/6250000000000 : ℝ)*(upper2) + (207910439/100000000000000 : ℝ)*(upper5) + (331267898531843/50000000000000 : ℝ)*(major0) + (331267898531843/50000000000000 : ℝ)*(major1) + (662535406666113/100000000000000 : ℝ)*(major2) + (111499663/10000000000000 : ℝ)*(sp1) + (1247490593/100000000000000 : ℝ)*(sp2) + (898833929201859/100000000000000 : ℝ)*(sp4) + (898832351333129/100000000000000 : ℝ)*(sp5) + (449416121312341/50000000000000 : ℝ)*(sp6) + (85247421236113/20000000000000 : ℝ)*(sp7) + (85247421236113/20000000000000 : ℝ)*(f.failure) + (898834319599433/100000000000000 : ℝ)*(f.sum) + (16575079861847/16000000000000000000000000000 : ℝ)*base66 + (32763387933489/16000000000000000000000000000 : ℝ)*base68 + (8478989699821/8000000000000000000000000000 : ℝ)*base69 + (58401893517489/16000000000000000000000000000 : ℝ)*base72 + (6364512074153/16000000000000000000000000000 : ℝ)*base73 + (1498644252179/8000000000000000000000000000 : ℝ)*base76 + (22027317780179/8000000000000000000000000000 : ℝ)*base78 + (13941694387821/8000000000000000000000000000 : ℝ)*base79 + (1281045252179/4000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (100627/25000000000000000000 : ℝ)*base89 + (100627/25000000000000000000 : ℝ)*base91 + (100627/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1360_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (387/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13371/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1360_s1_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-247596981/1250000000 : ℝ)*x 0 + (1408537899/2500000000 : ℝ)*x 1 + (5053495671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247596981/1250000000 : ℝ)^135 ≤ (5988891019693/50000000000000 : ℝ)^103 := by
    have hnat : (247596981 : ℕ)^135*50000000000000^103 ≤ 5988891019693^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247596981 1250000000 5988891019693 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1408537899/2500000000 : ℝ)^135 ≤ (47142871498683/100000000000000 : ℝ)^103 := by
    have hnat : (1408537899 : ℕ)^135*100000000000000^103 ≤ 47142871498683^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408537899 2500000000 47142871498683 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5053495671/10000000000 : ℝ)^135 ≤ (255495915311/625000000000 : ℝ)^103 := by
    have hnat : (5053495671 : ℕ)^135*625000000000^103 ≤ 255495915311^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053495671 10000000000 255495915311 625000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247596981/1250000000 : ℝ), (1408537899/2500000000 : ℝ), (5053495671/10000000000 : ℝ)] ![(5988891019693/50000000000000 : ℝ), (47142871498683/100000000000000 : ℝ), (255495915311/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247596981/1250000000 : ℝ)|^135 ≤ (5988891019693/50000000000000 : ℝ)^103
        have hw : |(-247596981/1250000000 : ℝ)|=(247596981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1408537899/2500000000 : ℝ)|^135 ≤ (47142871498683/100000000000000 : ℝ)^103
        have hw : |(1408537899/2500000000 : ℝ)|=(1408537899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5053495671/10000000000 : ℝ)|^135 ≤ (255495915311/625000000000 : ℝ)^103
        have hw : |(5053495671/10000000000 : ℝ)|=(5053495671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s1_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5403845841/10000000000 : ℝ)*x 0 + (-286269467/1250000000 : ℝ)*x 1 + (5053496563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403845841/10000000000 : ℝ)^135 ≤ (22316660782773/50000000000000 : ℝ)^103 := by
    have hnat : (5403845841 : ℕ)^135*50000000000000^103 ≤ 22316660782773^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403845841 10000000000 22316660782773 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286269467/1250000000 : ℝ)^135 ≤ (1448732250987/10000000000000 : ℝ)^103 := by
    have hnat : (286269467 : ℕ)^135*10000000000000^103 ≤ 1448732250987^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286269467 1250000000 1448732250987 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5053496563/10000000000 : ℝ)^135 ≤ (40879355907197/100000000000000 : ℝ)^103 := by
    have hnat : (5053496563 : ℕ)^135*100000000000000^103 ≤ 40879355907197^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053496563 10000000000 40879355907197 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403845841/10000000000 : ℝ), (-286269467/1250000000 : ℝ), (5053496563/10000000000 : ℝ)] ![(22316660782773/50000000000000 : ℝ), (1448732250987/10000000000000 : ℝ), (40879355907197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403845841/10000000000 : ℝ)|^135 ≤ (22316660782773/50000000000000 : ℝ)^103
        have hw : |(5403845841/10000000000 : ℝ)|=(5403845841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-286269467/1250000000 : ℝ)|^135 ≤ (1448732250987/10000000000000 : ℝ)^103
        have hw : |(-286269467/1250000000 : ℝ)|=(286269467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5053496563/10000000000 : ℝ)|^135 ≤ (40879355907197/100000000000000 : ℝ)^103
        have hw : |(5053496563/10000000000 : ℝ)|=(5053496563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s1_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5403846007/10000000000 : ℝ)*x 0 + (5053495843/10000000000 : ℝ)*x 1 + (-2290156441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403846007/10000000000 : ℝ)^135 ≤ (44633323362599/100000000000000 : ℝ)^103 := by
    have hnat : (5403846007 : ℕ)^135*100000000000000^103 ≤ 44633323362599^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403846007 10000000000 44633323362599 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5053495843/10000000000 : ℝ)^135 ≤ (40879348273391/100000000000000 : ℝ)^103 := by
    have hnat : (5053495843 : ℕ)^135*100000000000000^103 ≤ 40879348273391^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053495843 10000000000 40879348273391 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2290156441/10000000000 : ℝ)^135 ≤ (14487328355197/100000000000000 : ℝ)^103 := by
    have hnat : (2290156441 : ℕ)^135*100000000000000^103 ≤ 14487328355197^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290156441 10000000000 14487328355197 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403846007/10000000000 : ℝ), (5053495843/10000000000 : ℝ), (-2290156441/10000000000 : ℝ)] ![(44633323362599/100000000000000 : ℝ), (40879348273391/100000000000000 : ℝ), (14487328355197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403846007/10000000000 : ℝ)|^135 ≤ (44633323362599/100000000000000 : ℝ)^103
        have hw : |(5403846007/10000000000 : ℝ)|=(5403846007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5053495843/10000000000 : ℝ)|^135 ≤ (40879348273391/100000000000000 : ℝ)^103
        have hw : |(5053495843/10000000000 : ℝ)|=(5053495843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2290156441/10000000000 : ℝ)|^135 ≤ (14487328355197/100000000000000 : ℝ)^103
        have hw : |(-2290156441/10000000000 : ℝ)|=(2290156441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s1_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1072273123/2500000000 : ℝ)*x 0 + (371703973/1000000000 : ℝ)*x 1 + (1235375849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072273123/2500000000 : ℝ)^135 ≤ (824306736799/2500000000000 : ℝ)^103 := by
    have hnat : (1072273123 : ℕ)^135*2500000000000^103 ≤ 824306736799^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072273123 2500000000 824306736799 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371703973/1000000000 : ℝ)^135 ≤ (2733167432073/10000000000000 : ℝ)^103 := by
    have hnat : (371703973 : ℕ)^135*10000000000000^103 ≤ 2733167432073^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371703973 1000000000 2733167432073 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1235375849/2500000000 : ℝ)^135 ≤ (4962007023733/12500000000000 : ℝ)^103 := by
    have hnat : (1235375849 : ℕ)^135*12500000000000^103 ≤ 4962007023733^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235375849 2500000000 4962007023733 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072273123/2500000000 : ℝ), (371703973/1000000000 : ℝ), (1235375849/2500000000 : ℝ)] ![(824306736799/2500000000000 : ℝ), (2733167432073/10000000000000 : ℝ), (4962007023733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072273123/2500000000 : ℝ)|^135 ≤ (824306736799/2500000000000 : ℝ)^103
        have hw : |(1072273123/2500000000 : ℝ)|=(1072273123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(371703973/1000000000 : ℝ)|^135 ≤ (2733167432073/10000000000000 : ℝ)^103
        have hw : |(371703973/1000000000 : ℝ)|=(371703973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1235375849/2500000000 : ℝ)|^135 ≤ (4962007023733/12500000000000 : ℝ)^103
        have hw : |(1235375849/2500000000 : ℝ)|=(1235375849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s1_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-990640203/5000000000 : ℝ)*x 0 + (5060681523/10000000000 : ℝ)*x 1 + (1406709211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990640203/5000000000 : ℝ)^135 ≤ (5990890586423/50000000000000 : ℝ)^103 := by
    have hnat : (990640203 : ℕ)^135*50000000000000^103 ≤ 5990890586423^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990640203 5000000000 5990890586423 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5060681523/10000000000 : ℝ)^135 ≤ (40955551323149/100000000000000 : ℝ)^103 := by
    have hnat : (5060681523 : ℕ)^135*100000000000000^103 ≤ 40955551323149^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060681523 10000000000 40955551323149 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1406709211/2500000000 : ℝ)^135 ≤ (23531333748967/50000000000000 : ℝ)^103 := by
    have hnat : (1406709211 : ℕ)^135*50000000000000^103 ≤ 23531333748967^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406709211 2500000000 23531333748967 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-990640203/5000000000 : ℝ), (5060681523/10000000000 : ℝ), (1406709211/2500000000 : ℝ)] ![(5990890586423/50000000000000 : ℝ), (40955551323149/100000000000000 : ℝ), (23531333748967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-990640203/5000000000 : ℝ)|^135 ≤ (5990890586423/50000000000000 : ℝ)^103
        have hw : |(-990640203/5000000000 : ℝ)|=(990640203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5060681523/10000000000 : ℝ)|^135 ≤ (40955551323149/100000000000000 : ℝ)^103
        have hw : |(5060681523/10000000000 : ℝ)|=(5060681523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1406709211/2500000000 : ℝ)|^135 ≤ (23531333748967/50000000000000 : ℝ)^103
        have hw : |(1406709211/2500000000 : ℝ)|=(1406709211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s1_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1050589921/2000000000 : ℝ)*x 0 + (-1716815269/10000000000 : ℝ)*x 1 + (562683691/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050589921/2000000000 : ℝ)^135 ≤ (860138159783/2000000000000 : ℝ)^103 := by
    have hnat : (1050589921 : ℕ)^135*2000000000000^103 ≤ 860138159783^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050589921 2000000000 860138159783 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716815269/10000000000 : ℝ)^135 ≤ (9930423776213/100000000000000 : ℝ)^103 := by
    have hnat : (1716815269 : ℕ)^135*100000000000000^103 ≤ 9930423776213^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716815269 10000000000 9930423776213 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562683691/1000000000 : ℝ)^135 ≤ (47062668221457/100000000000000 : ℝ)^103 := by
    have hnat : (562683691 : ℕ)^135*100000000000000^103 ≤ 47062668221457^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562683691 1000000000 47062668221457 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050589921/2000000000 : ℝ), (-1716815269/10000000000 : ℝ), (562683691/1000000000 : ℝ)] ![(860138159783/2000000000000 : ℝ), (9930423776213/100000000000000 : ℝ), (47062668221457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050589921/2000000000 : ℝ)|^135 ≤ (860138159783/2000000000000 : ℝ)^103
        have hw : |(1050589921/2000000000 : ℝ)|=(1050589921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1716815269/10000000000 : ℝ)|^135 ≤ (9930423776213/100000000000000 : ℝ)^103
        have hw : |(-1716815269/10000000000 : ℝ)|=(1716815269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562683691/1000000000 : ℝ)|^135 ≤ (47062668221457/100000000000000 : ℝ)^103
        have hw : |(562683691/1000000000 : ℝ)|=(562683691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s1_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2626474749/5000000000 : ℝ)*x 0 + (1406709249/2500000000 : ℝ)*x 1 + (-26825239/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626474749/5000000000 : ℝ)^135 ≤ (10751726710239/25000000000000 : ℝ)^103 := by
    have hnat : (2626474749 : ℕ)^135*25000000000000^103 ≤ 10751726710239^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626474749 5000000000 10751726710239 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1406709249/2500000000 : ℝ)^135 ≤ (4706266916423/10000000000000 : ℝ)^103 := by
    have hnat : (1406709249 : ℕ)^135*10000000000000^103 ≤ 4706266916423^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406709249 2500000000 4706266916423 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26825239/156250000 : ℝ)^135 ≤ (9930423980907/100000000000000 : ℝ)^103 := by
    have hnat : (26825239 : ℕ)^135*100000000000000^103 ≤ 9930423980907^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26825239 156250000 9930423980907 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626474749/5000000000 : ℝ), (1406709249/2500000000 : ℝ), (-26825239/156250000 : ℝ)] ![(10751726710239/25000000000000 : ℝ), (4706266916423/10000000000000 : ℝ), (9930423980907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626474749/5000000000 : ℝ)|^135 ≤ (10751726710239/25000000000000 : ℝ)^103
        have hw : |(2626474749/5000000000 : ℝ)|=(2626474749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1406709249/2500000000 : ℝ)|^135 ≤ (4706266916423/10000000000000 : ℝ)^103
        have hw : |(1406709249/2500000000 : ℝ)|=(1406709249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26825239/156250000 : ℝ)|^135 ≤ (9930423980907/100000000000000 : ℝ)^103
        have hw : |(-26825239/156250000 : ℝ)|=(26825239/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s1_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2145078559/5000000000 : ℝ)*x 0 + (197054063/400000000 : ℝ)*x 1 + (746492421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145078559/5000000000 : ℝ)^135 ≤ (1319319874197/4000000000000 : ℝ)^103 := by
    have hnat : (2145078559 : ℕ)^135*4000000000000^103 ≤ 1319319874197^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145078559 5000000000 1319319874197 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197054063/400000000 : ℝ)^135 ≤ (39536599558589/100000000000000 : ℝ)^103 := by
    have hnat : (197054063 : ℕ)^135*100000000000000^103 ≤ 39536599558589^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197054063 400000000 39536599558589 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (746492421/2000000000 : ℝ)^135 ≤ (27480403572149/100000000000000 : ℝ)^103 := by
    have hnat : (746492421 : ℕ)^135*100000000000000^103 ≤ 27480403572149^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746492421 2000000000 27480403572149 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145078559/5000000000 : ℝ), (197054063/400000000 : ℝ), (746492421/2000000000 : ℝ)] ![(1319319874197/4000000000000 : ℝ), (39536599558589/100000000000000 : ℝ), (27480403572149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145078559/5000000000 : ℝ)|^135 ≤ (1319319874197/4000000000000 : ℝ)^103
        have hw : |(2145078559/5000000000 : ℝ)|=(2145078559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197054063/400000000 : ℝ)|^135 ≤ (39536599558589/100000000000000 : ℝ)^103
        have hw : |(197054063/400000000 : ℝ)|=(197054063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(746492421/2000000000 : ℝ)|^135 ≤ (27480403572149/100000000000000 : ℝ)^103
        have hw : |(746492421/2000000000 : ℝ)|=(746492421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1411/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (604/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (387/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (387/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (387/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (387/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (387/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (387/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (387/25000 : ℝ) ^ (4319/1024 : ℝ) ≤ (463333839047/20000000000000000000 : ℝ) := by
    have hpowers : (387/25000 : ℝ)^4319 ≤ (463333839047/20000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4319*20000000000000000000^1024 ≤ 463333839047^1024*25000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 25000 463333839047 20000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/25000 : ℝ)) (X := (463333839047/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13371/50000 : ℝ) ^ (4319/1024 : ℝ) ≤ (383736916146953679/100000000000000000000 : ℝ) := by
    have hpowers : (13371/50000 : ℝ)^4319 ≤ (383736916146953679/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13371 : ℕ)^4319*100000000000000000000^1024 ≤ 383736916146953679^1024*50000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13371 50000 383736916146953679 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13371/50000 : ℝ)) (X := (383736916146953679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000463333839047/10000000000000000000 : ℝ) ≤ (2500000027463177/2500000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (10000000463333839047/10000000000000000000 : ℝ)^1024 ≤ (2500000027463177/2500000000000000 : ℝ)^4319 := by
      have hnat : (10000000463333839047 : ℕ)^1024*2500000000000000^4319 ≤ 2500000027463177^4319*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000463333839047 10000000000000000000 2500000027463177 2500000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000027463177/2500000000000000 : ℝ)) (X := (10000000463333839047/10000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50191869616408074457/50000000000000000000 : ℝ) ≤ (5004542429656429/5000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50191869616408074457/50000000000000000000 : ℝ)^1024 ≤ (5004542429656429/5000000000000000 : ℝ)^4319 := by
      have hnat : (50191869616408074457 : ℕ)^1024*5000000000000000^4319 ≤ 5004542429656429^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50191869616408074457 50000000000000000000 5004542429656429 5000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004542429656429/5000000000000000 : ℝ)) (X := (50191869616408074457/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50383736916146953679/50000000000000000000 : ℝ) ≤ (626135600548313/625000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50383736916146953679/50000000000000000000 : ℝ)^1024 ≤ (626135600548313/625000000000000 : ℝ)^4319 := by
      have hnat : (50383736916146953679 : ℕ)^1024*625000000000000^4319 ≤ 626135600548313^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50383736916146953679 50000000000000000000 626135600548313 625000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626135600548313/625000000000000 : ℝ)) (X := (50383736916146953679/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(463333839047/20000000000000000000 : ℝ) ≤ ((807409860202886221/807500000000000000 : ℝ)+2*(4658845877/1292000000000 : ℝ)*(387/25000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (807409860202886221/807500000000000000 : ℝ)+2*(4658845877/1292000000000 : ℝ)*(387/25000 : ℝ)=(2500000027463177/2500000000000000 : ℝ) by norm_num, show 1+2*(463333839047/20000000000000000000 : ℝ)=(10000000463333839047/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(383736916146953679/100000000000000000000 : ℝ)+(463333839047/20000000000000000000 : ℝ) ≤ ((807409860202886221/807500000000000000 : ℝ)+(4658845877/1292000000000 : ℝ)*((13371/50000 : ℝ)+(387/25000 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (807409860202886221/807500000000000000 : ℝ)+(4658845877/1292000000000 : ℝ)*((13371/50000 : ℝ)+(387/25000 : ℝ))=(5004542429656429/5000000000000000 : ℝ) by norm_num, show 1+(383736916146953679/100000000000000000000 : ℝ)+(463333839047/20000000000000000000 : ℝ)=(50191869616408074457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(383736916146953679/100000000000000000000 : ℝ) ≤ ((807409860202886221/807500000000000000 : ℝ)+2*(4658845877/1292000000000 : ℝ)*(13371/50000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (807409860202886221/807500000000000000 : ℝ)+2*(4658845877/1292000000000 : ℝ)*(13371/50000 : ℝ)=(626135600548313/625000000000000 : ℝ) by norm_num, show 1+2*(383736916146953679/100000000000000000000 : ℝ)=(50383736916146953679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (807409860202886221/807500000000000000 : ℝ)*(X 1 0+X 2 0)+(4658845877/1292000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (387/25000 : ℝ)) (hi := (13371/50000 : ℝ)) (c := (807409860202886221/807500000000000000 : ℝ)) (alpha := (4658845877/1292000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (807409860202886221/807500000000000000 : ℝ)*(X 0 1+X 2 1)+(4658845877/1292000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (387/25000 : ℝ)) (hi := (13371/50000 : ℝ)) (c := (807409860202886221/807500000000000000 : ℝ)) (alpha := (4658845877/1292000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (807409860202886221/807500000000000000 : ℝ)*(X 0 2+X 1 2)+(4658845877/1292000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (387/25000 : ℝ)) (hi := (13371/50000 : ℝ)) (c := (807409860202886221/807500000000000000 : ℝ)) (alpha := (4658845877/1292000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-247596981/1250000000 : ℝ)*X 0 0+(1408537899/2500000000 : ℝ)*X 0 1+(5053495671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5403845841/10000000000 : ℝ)*X 1 0+(-286269467/1250000000 : ℝ)*X 1 1+(5053496563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5403846007/10000000000 : ℝ)*X 2 0+(5053495843/10000000000 : ℝ)*X 2 1+(-2290156441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1072273123/2500000000 : ℝ)*X 0 0+(371703973/1000000000 : ℝ)*X 0 1+(1235375849/2500000000 : ℝ)*X 0 2+(1072273123/2500000000 : ℝ)*X 1 0+(371703973/1000000000 : ℝ)*X 1 1+(1235375849/2500000000 : ℝ)*X 1 2+(1072273123/2500000000 : ℝ)*X 2 0+(371703973/1000000000 : ℝ)*X 2 1+(1235375849/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-990640203/5000000000 : ℝ)*X 0 0+(5060681523/10000000000 : ℝ)*X 0 1+(1406709211/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050589921/2000000000 : ℝ)*X 1 0+(-1716815269/10000000000 : ℝ)*X 1 1+(562683691/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626474749/5000000000 : ℝ)*X 2 0+(1406709249/2500000000 : ℝ)*X 2 1+(-26825239/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2145078559/5000000000 : ℝ)*X 0 0+(197054063/400000000 : ℝ)*X 0 1+(746492421/2000000000 : ℝ)*X 0 2+(2145078559/5000000000 : ℝ)*X 1 0+(197054063/400000000 : ℝ)*X 1 1+(746492421/2000000000 : ℝ)*X 1 2+(2145078559/5000000000 : ℝ)*X 2 0+(197054063/400000000 : ℝ)*X 2 1+(746492421/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (596330122857089870427/80750000000000000000000000 : ℝ) := by norm_num
    linear_combination (902711/4000000000000 : ℝ)*(base16) + (34809027/3125000000000 : ℝ)*(base19) + (1193630799/100000000000000 : ℝ)*(base23) + (1153691/50000000000000 : ℝ)*(upper2) + (3402383/1562500000000 : ℝ)*(upper3) + (253889987671883/20000000000000 : ℝ)*(major0) + (253889987671883/20000000000000 : ℝ)*(major1) + (253889987671883/20000000000000 : ℝ)*(major2) + (1722200872970027/100000000000000 : ℝ)*(sp0) + (1722208029122737/100000000000000 : ℝ)*(sp1) + (1722207971948577/100000000000000 : ℝ)*(sp2) + (816686693518807/100000000000000 : ℝ)*(sp3) + (8292609349/100000000000000 : ℝ)*(sp4) + (460383/12207031250 : ℝ)*(sp7) + (408345232488171/50000000000000 : ℝ)*(f.failure) + (107638072848711/6250000000000 : ℝ)*(f.sum) + (1342622338971/323000000000000000000000000 : ℝ)*base66 + (4251990629150857/16150000000000000000000000000000 : ℝ)*base68 + (60393930345449143/16150000000000000000000000000000 : ℝ)*base69 + (15831629663849143/16150000000000000000000000000000 : ℝ)*base71 + (1432363746819/323000000000000000000000000 : ℝ)*base74 + (22380395571250857/16150000000000000000000000000000 : ℝ)*base76 + (70502686828549143/16150000000000000000000000000000 : ℝ)*base77 + (63291445369950857/16150000000000000000000000000000 : ℝ)*base80 + (89226107881/32300000000000000000000000 : ℝ)*base82 + (373591/62500000000000000000 : ℝ)*base90 + (373591/62500000000000000000 : ℝ)*base92 + (373591/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (541025445267250435473/80750000000000000000000000 : ℝ) := by norm_num
    linear_combination (35675927/50000000000000 : ℝ)*(base1) + (681836233/50000000000000 : ℝ)*(base19) + (1326485993/100000000000000 : ℝ)*(base23) + (157523283/100000000000000 : ℝ)*(upper3) + (18427163/12500000000000 : ℝ)*(upper5) + (130194912734229/10000000000000 : ℝ)*(major0) + (130194912734229/10000000000000 : ℝ)*(major1) + (130194912734229/10000000000000 : ℝ)*(major2) + (3578519993/50000000000000 : ℝ)*(sp1) + (355748999/5000000000000 : ℝ)*(sp2) + (441574886104499/25000000000000 : ℝ)*(sp4) + (1766290952353691/100000000000000 : ℝ)*(sp5) + (220786378950021/12500000000000 : ℝ)*(sp6) + (837598486933059/100000000000000 : ℝ)*(sp7) + (837598558284913/100000000000000 : ℝ)*(f.failure) + (883149736533071/50000000000000 : ℝ)*(f.sum) + (146296742157/80750000000000000000000000 : ℝ)*base66 + (92531992793308609/8075000000000000000000000000000 : ℝ)*base67 + (1060228693641391/8075000000000000000000000000000 : ℝ)*base70 + (780625632558609/8075000000000000000000000000000 : ℝ)*base71 + (3053000643/1615000000000000000000000 : ℝ)*base73 + (49257144498441391/8075000000000000000000000000000 : ℝ)*base76 + (17506949954666391/8075000000000000000000000000000 : ℝ)*base78 + (74810997021308609/8075000000000000000000000000000 : ℝ)*base79 + (1527646285051/323000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (524173/125000000000000000000 : ℝ)*base90 + (524173/125000000000000000000 : ℝ)*base92 + (524173/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1360_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (604/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1360_s2_0 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009692737/5000000000 : ℝ)*x 0 + (5474924091/10000000000 : ℝ)*x 1 + (1037593299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009692737/5000000000 : ℝ)^135 ≤ (3071178198377/25000000000000 : ℝ)^103 := by
    have hnat : (1009692737 : ℕ)^135*25000000000000^103 ≤ 3071178198377^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009692737 5000000000 3071178198377 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474924091/10000000000 : ℝ)^135 ≤ (11351088799407/25000000000000 : ℝ)^103 := by
    have hnat : (5474924091 : ℕ)^135*25000000000000^103 ≤ 11351088799407^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474924091 10000000000 11351088799407 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037593299/2000000000 : ℝ)^135 ≤ (42310932001131/100000000000000 : ℝ)^103 := by
    have hnat : (1037593299 : ℕ)^135*100000000000000^103 ≤ 42310932001131^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037593299 2000000000 42310932001131 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009692737/5000000000 : ℝ), (5474924091/10000000000 : ℝ), (1037593299/2000000000 : ℝ)] ![(3071178198377/25000000000000 : ℝ), (11351088799407/25000000000000 : ℝ), (42310932001131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009692737/5000000000 : ℝ)|^135 ≤ (3071178198377/25000000000000 : ℝ)^103
        have hw : |(-1009692737/5000000000 : ℝ)|=(1009692737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474924091/10000000000 : ℝ)|^135 ≤ (11351088799407/25000000000000 : ℝ)^103
        have hw : |(5474924091/10000000000 : ℝ)|=(5474924091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037593299/2000000000 : ℝ)|^135 ≤ (42310932001131/100000000000000 : ℝ)^103
        have hw : |(1037593299/2000000000 : ℝ)|=(1037593299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s2_1 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2682349913/5000000000 : ℝ)*x 0 + (-1083757583/5000000000 : ℝ)*x 1 + (5187966839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682349913/5000000000 : ℝ)^135 ≤ (44210019335861/100000000000000 : ℝ)^103 := by
    have hnat : (2682349913 : ℕ)^135*100000000000000^103 ≤ 44210019335861^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682349913 5000000000 44210019335861 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083757583/5000000000 : ℝ)^135 ≤ (1347904496083/10000000000000 : ℝ)^103 := by
    have hnat : (1083757583 : ℕ)^135*10000000000000^103 ≤ 1347904496083^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083757583 5000000000 1347904496083 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5187966839/10000000000 : ℝ)^135 ≤ (42310935678273/100000000000000 : ℝ)^103 := by
    have hnat : (5187966839 : ℕ)^135*100000000000000^103 ≤ 42310935678273^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187966839 10000000000 42310935678273 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682349913/5000000000 : ℝ), (-1083757583/5000000000 : ℝ), (5187966839/10000000000 : ℝ)] ![(44210019335861/100000000000000 : ℝ), (1347904496083/10000000000000 : ℝ), (42310935678273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682349913/5000000000 : ℝ)|^135 ≤ (44210019335861/100000000000000 : ℝ)^103
        have hw : |(2682349913/5000000000 : ℝ)|=(2682349913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1083757583/5000000000 : ℝ)|^135 ≤ (1347904496083/10000000000000 : ℝ)^103
        have hw : |(-1083757583/5000000000 : ℝ)|=(1083757583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5187966839/10000000000 : ℝ)|^135 ≤ (42310935678273/100000000000000 : ℝ)^103
        have hw : |(5187966839/10000000000 : ℝ)|=(5187966839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s2_2 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5364699879/10000000000 : ℝ)*x 0 + (2593983387/5000000000 : ℝ)*x 1 + (-1083757591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364699879/10000000000 : ℝ)^135 ≤ (11052504977081/25000000000000 : ℝ)^103 := by
    have hnat : (5364699879 : ℕ)^135*25000000000000^103 ≤ 11052504977081^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364699879 10000000000 11052504977081 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593983387/5000000000 : ℝ)^135 ≤ (5288866872933/12500000000000 : ℝ)^103 := by
    have hnat : (2593983387 : ℕ)^135*12500000000000^103 ≤ 5288866872933^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593983387 5000000000 5288866872933 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083757591/5000000000 : ℝ)^135 ≤ (336976127281/2500000000000 : ℝ)^103 := by
    have hnat : (1083757591 : ℕ)^135*2500000000000^103 ≤ 336976127281^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083757591 5000000000 336976127281 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364699879/10000000000 : ℝ), (2593983387/5000000000 : ℝ), (-1083757591/5000000000 : ℝ)] ![(11052504977081/25000000000000 : ℝ), (5288866872933/12500000000000 : ℝ), (336976127281/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364699879/10000000000 : ℝ)|^135 ≤ (11052504977081/25000000000000 : ℝ)^103
        have hw : |(5364699879/10000000000 : ℝ)|=(5364699879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593983387/5000000000 : ℝ)|^135 ≤ (5288866872933/12500000000000 : ℝ)^103
        have hw : |(2593983387/5000000000 : ℝ)|=(2593983387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083757591/5000000000 : ℝ)|^135 ≤ (336976127281/2500000000000 : ℝ)^103
        have hw : |(-1083757591/5000000000 : ℝ)|=(1083757591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s2_3 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4316148371/10000000000 : ℝ)*x 0 + (4023393831/10000000000 : ℝ)*x 1 + (4628519599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316148371/10000000000 : ℝ)^135 ≤ (33245146112781/100000000000000 : ℝ)^103 := by
    have hnat : (4316148371 : ℕ)^135*100000000000000^103 ≤ 33245146112781^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316148371 10000000000 33245146112781 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023393831/10000000000 : ℝ)^135 ≤ (1212851145349/4000000000000 : ℝ)^103 := by
    have hnat : (4023393831 : ℕ)^135*4000000000000^103 ≤ 1212851145349^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023393831 10000000000 1212851145349 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4628519599/10000000000 : ℝ)^135 ≤ (36433575238241/100000000000000 : ℝ)^103 := by
    have hnat : (4628519599 : ℕ)^135*100000000000000^103 ≤ 36433575238241^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4628519599 10000000000 36433575238241 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316148371/10000000000 : ℝ), (4023393831/10000000000 : ℝ), (4628519599/10000000000 : ℝ)] ![(33245146112781/100000000000000 : ℝ), (1212851145349/4000000000000 : ℝ), (36433575238241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316148371/10000000000 : ℝ)|^135 ≤ (33245146112781/100000000000000 : ℝ)^103
        have hw : |(4316148371/10000000000 : ℝ)|=(4316148371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023393831/10000000000 : ℝ)|^135 ≤ (1212851145349/4000000000000 : ℝ)^103
        have hw : |(4023393831/10000000000 : ℝ)|=(4023393831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4628519599/10000000000 : ℝ)|^135 ≤ (36433575238241/100000000000000 : ℝ)^103
        have hw : |(4628519599/10000000000 : ℝ)|=(4628519599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s2_4 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2019446407/10000000000 : ℝ)*x 0 + (2594865673/5000000000 : ℝ)*x 1 + (2736571817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2019446407/10000000000 : ℝ)^135 ≤ (12285198637593/100000000000000 : ℝ)^103 := by
    have hnat : (2019446407 : ℕ)^135*100000000000000^103 ≤ 12285198637593^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019446407 10000000000 12285198637593 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2594865673/5000000000 : ℝ)^135 ≤ (21164899068671/50000000000000 : ℝ)^103 := by
    have hnat : (2594865673 : ℕ)^135*50000000000000^103 ≤ 21164899068671^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594865673 5000000000 21164899068671 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736571817/5000000000 : ℝ)^135 ≤ (45385003213363/100000000000000 : ℝ)^103 := by
    have hnat : (2736571817 : ℕ)^135*100000000000000^103 ≤ 45385003213363^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736571817 5000000000 45385003213363 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2019446407/10000000000 : ℝ), (2594865673/5000000000 : ℝ), (2736571817/5000000000 : ℝ)] ![(12285198637593/100000000000000 : ℝ), (21164899068671/50000000000000 : ℝ), (45385003213363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2019446407/10000000000 : ℝ)|^135 ≤ (12285198637593/100000000000000 : ℝ)^103
        have hw : |(-2019446407/10000000000 : ℝ)|=(2019446407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2594865673/5000000000 : ℝ)|^135 ≤ (21164899068671/50000000000000 : ℝ)^103
        have hw : |(2594865673/5000000000 : ℝ)|=(2594865673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736571817/5000000000 : ℝ)|^135 ≤ (45385003213363/100000000000000 : ℝ)^103
        have hw : |(2736571817/5000000000 : ℝ)|=(2736571817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s2_5 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2645296967/5000000000 : ℝ)*x 0 + (-1882338087/10000000000 : ℝ)*x 1 + (1368285897/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645296967/5000000000 : ℝ)^135 ≤ (4341131017193/10000000000000 : ℝ)^103 := by
    have hnat : (2645296967 : ℕ)^135*10000000000000^103 ≤ 4341131017193^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645296967 5000000000 4341131017193 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882338087/10000000000 : ℝ)^135 ≤ (11203687096643/100000000000000 : ℝ)^103 := by
    have hnat : (1882338087 : ℕ)^135*100000000000000^103 ≤ 11203687096643^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882338087 10000000000 11203687096643 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368285897/2500000000 : ℝ)^135 ≤ (45385002713409/100000000000000 : ℝ)^103 := by
    have hnat : (1368285897 : ℕ)^135*100000000000000^103 ≤ 45385002713409^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368285897 2500000000 45385002713409 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645296967/5000000000 : ℝ), (-1882338087/10000000000 : ℝ), (1368285897/2500000000 : ℝ)] ![(4341131017193/10000000000000 : ℝ), (11203687096643/100000000000000 : ℝ), (45385002713409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645296967/5000000000 : ℝ)|^135 ≤ (4341131017193/10000000000000 : ℝ)^103
        have hw : |(2645296967/5000000000 : ℝ)|=(2645296967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1882338087/10000000000 : ℝ)|^135 ≤ (11203687096643/100000000000000 : ℝ)^103
        have hw : |(-1882338087/10000000000 : ℝ)|=(1882338087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368285897/2500000000 : ℝ)|^135 ≤ (45385002713409/100000000000000 : ℝ)^103
        have hw : |(1368285897/2500000000 : ℝ)|=(1368285897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s2_6 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2645296951/5000000000 : ℝ)*x 0 + (2736571819/5000000000 : ℝ)*x 1 + (-1882338061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645296951/5000000000 : ℝ)^135 ≤ (21705654913891/50000000000000 : ℝ)^103 := by
    have hnat : (2645296951 : ℕ)^135*50000000000000^103 ≤ 21705654913891^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645296951 5000000000 21705654913891 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736571819/5000000000 : ℝ)^135 ≤ (45385003256837/100000000000000 : ℝ)^103 := by
    have hnat : (2736571819 : ℕ)^135*100000000000000^103 ≤ 45385003256837^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736571819 5000000000 45385003256837 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882338061/10000000000 : ℝ)^135 ≤ (11203686893813/100000000000000 : ℝ)^103 := by
    have hnat : (1882338061 : ℕ)^135*100000000000000^103 ≤ 11203686893813^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882338061 10000000000 11203686893813 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645296951/5000000000 : ℝ), (2736571819/5000000000 : ℝ), (-1882338061/10000000000 : ℝ)] ![(21705654913891/50000000000000 : ℝ), (45385003256837/100000000000000 : ℝ), (11203686893813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645296951/5000000000 : ℝ)|^135 ≤ (21705654913891/50000000000000 : ℝ)^103
        have hw : |(2645296951/5000000000 : ℝ)|=(2645296951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736571819/5000000000 : ℝ)|^135 ≤ (45385003256837/100000000000000 : ℝ)^103
        have hw : |(2736571819/5000000000 : ℝ)|=(2736571819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1882338061/10000000000 : ℝ)|^135 ≤ (11203686893813/100000000000000 : ℝ)^103
        have hw : |(-1882338061/10000000000 : ℝ)|=(1882338061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1360_s2_7 (p : ℝ) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (863255431/2000000000 : ℝ)*x 0 + (9249597/20000000 : ℝ)*x 1 + (4027147831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863255431/2000000000 : ℝ)^135 ≤ (33246446259449/100000000000000 : ℝ)^103 := by
    have hnat : (863255431 : ℕ)^135*100000000000000^103 ≤ 33246446259449^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863255431 2000000000 33246446259449 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9249597/20000000 : ℝ)^135 ≤ (2274699325497/6250000000000 : ℝ)^103 := by
    have hnat : (9249597 : ℕ)^135*6250000000000^103 ≤ 2274699325497^103*20000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9249597 20000000 2274699325497 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027147831/10000000000 : ℝ)^135 ≤ (758959113093/2500000000000 : ℝ)^103 := by
    have hnat : (4027147831 : ℕ)^135*2500000000000^103 ≤ 758959113093^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027147831 10000000000 758959113093 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863255431/2000000000 : ℝ), (9249597/20000000 : ℝ), (4027147831/10000000000 : ℝ)] ![(33246446259449/100000000000000 : ℝ), (2274699325497/6250000000000 : ℝ), (758959113093/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863255431/2000000000 : ℝ)|^135 ≤ (33246446259449/100000000000000 : ℝ)^103
        have hw : |(863255431/2000000000 : ℝ)|=(863255431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9249597/20000000 : ℝ)|^135 ≤ (2274699325497/6250000000000 : ℝ)^103
        have hw : |(9249597/20000000 : ℝ)|=(9249597/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027147831/10000000000 : ℝ)|^135 ≤ (758959113093/2500000000000 : ℝ)^103
        have hw : |(4027147831/10000000000 : ℝ)|=(4027147831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1360_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (604/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9967/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (604/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1411/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (604/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1411/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (604/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1411/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (604/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1411/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (604/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1411/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (604/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1411/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1411/20000 : ℝ) ^ (4319/1024 : ℝ) ≤ (1390661109911351/100000000000000000000 : ℝ) := by
    have hpowers : (1411/20000 : ℝ)^4319 ≤ (1390661109911351/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1411 : ℕ)^4319*100000000000000000000^1024 ≤ 1390661109911351^1024*20000^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 20000 1390661109911351 100000000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/20000 : ℝ)) (X := (1390661109911351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (604/3125 : ℝ) ^ (4319/1024 : ℝ) ≤ (12195739855072273/12500000000000000000 : ℝ) := by
    have hpowers : (604/3125 : ℝ)^4319 ≤ (12195739855072273/12500000000000000000 : ℝ)^1024 := by
      have hnat : (604 : ℕ)^4319*12500000000000000000^1024 ≤ 12195739855072273^1024*3125^4319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        604 3125 12195739855072273 12500000000000000000 4319 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (604/3125 : ℝ)) (X := (12195739855072273/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001390661109911351/50000000000000000000 : ℝ) ≤ (10000065942202757/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (50001390661109911351/50000000000000000000 : ℝ)^1024 ≤ (10000065942202757/10000000000000000 : ℝ)^4319 := by
      have hnat : (50001390661109911351 : ℕ)^1024*10000000000000000^4319 ≤ 10000065942202757^4319*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001390661109911351 50000000000000000000 10000065942202757 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000065942202757/10000000000000000 : ℝ)) (X := (50001390661109911351/50000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20019791315990097907/20000000000000000000 : ℝ) ≤ (10002345295440813/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (20019791315990097907/20000000000000000000 : ℝ)^1024 ≤ (10002345295440813/10000000000000000 : ℝ)^4319 := by
      have hnat : (20019791315990097907 : ℕ)^1024*10000000000000000^4319 ≤ 10002345295440813^4319*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20019791315990097907 20000000000000000000 10002345295440813 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002345295440813/10000000000000000 : ℝ)) (X := (20019791315990097907/20000000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6262195739855072273/6250000000000000000 : ℝ) ≤ (10004624648678869/10000000000000000 : ℝ) ^ (4319/1024 : ℝ) := by
    have hpowers : (6262195739855072273/6250000000000000000 : ℝ)^1024 ≤ (10004624648678869/10000000000000000 : ℝ)^4319 := by
      have hnat : (6262195739855072273 : ℕ)^1024*10000000000000000^4319 ≤ 10004624648678869^4319*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6262195739855072273 6250000000000000000 10004624648678869 10000000000000000 1024 4319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004624648678869/10000000000000000 : ℝ)) (X := (6262195739855072273/6250000000000000000 : ℝ)) (by norm_num) 4319 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1390661109911351/100000000000000000000 : ℝ) ≤ ((122698647634465466501/122730000000000000000 : ℝ)+2*(284919154757/153412500000000 : ℝ)*(1411/20000 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (122698647634465466501/122730000000000000000 : ℝ)+2*(284919154757/153412500000000 : ℝ)*(1411/20000 : ℝ)=(10000065942202757/10000000000000000 : ℝ) by norm_num, show 1+2*(1390661109911351/100000000000000000000 : ℝ)=(50001390661109911351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12195739855072273/12500000000000000000 : ℝ)+(1390661109911351/100000000000000000000 : ℝ) ≤ ((122698647634465466501/122730000000000000000 : ℝ)+(284919154757/153412500000000 : ℝ)*((604/3125 : ℝ)+(1411/20000 : ℝ)))^(4319/1024 : ℝ) := by
    rw [show (122698647634465466501/122730000000000000000 : ℝ)+(284919154757/153412500000000 : ℝ)*((604/3125 : ℝ)+(1411/20000 : ℝ))=(10002345295440813/10000000000000000 : ℝ) by norm_num, show 1+(12195739855072273/12500000000000000000 : ℝ)+(1390661109911351/100000000000000000000 : ℝ)=(20019791315990097907/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12195739855072273/12500000000000000000 : ℝ) ≤ ((122698647634465466501/122730000000000000000 : ℝ)+2*(284919154757/153412500000000 : ℝ)*(604/3125 : ℝ))^(4319/1024 : ℝ) := by
    rw [show (122698647634465466501/122730000000000000000 : ℝ)+2*(284919154757/153412500000000 : ℝ)*(604/3125 : ℝ)=(10004624648678869/10000000000000000 : ℝ) by norm_num, show 1+2*(12195739855072273/12500000000000000000 : ℝ)=(6262195739855072273/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (122698647634465466501/122730000000000000000 : ℝ)*(X 1 0+X 2 0)+(284919154757/153412500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1411/20000 : ℝ)) (hi := (604/3125 : ℝ)) (c := (122698647634465466501/122730000000000000000 : ℝ)) (alpha := (284919154757/153412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (122698647634465466501/122730000000000000000 : ℝ)*(X 0 1+X 2 1)+(284919154757/153412500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1411/20000 : ℝ)) (hi := (604/3125 : ℝ)) (c := (122698647634465466501/122730000000000000000 : ℝ)) (alpha := (284919154757/153412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (122698647634465466501/122730000000000000000 : ℝ)*(X 0 2+X 1 2)+(284919154757/153412500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4319/1024 : ℝ)) (lo := (1411/20000 : ℝ)) (hi := (604/3125 : ℝ)) (c := (122698647634465466501/122730000000000000000 : ℝ)) (alpha := (284919154757/153412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1009692737/5000000000 : ℝ)*X 0 0+(5474924091/10000000000 : ℝ)*X 0 1+(1037593299/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682349913/5000000000 : ℝ)*X 1 0+(-1083757583/5000000000 : ℝ)*X 1 1+(5187966839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364699879/10000000000 : ℝ)*X 2 0+(2593983387/5000000000 : ℝ)*X 2 1+(-1083757591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316148371/10000000000 : ℝ)*X 0 0+(4023393831/10000000000 : ℝ)*X 0 1+(4628519599/10000000000 : ℝ)*X 0 2+(4316148371/10000000000 : ℝ)*X 1 0+(4023393831/10000000000 : ℝ)*X 1 1+(4628519599/10000000000 : ℝ)*X 1 2+(4316148371/10000000000 : ℝ)*X 2 0+(4023393831/10000000000 : ℝ)*X 2 1+(4628519599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2019446407/10000000000 : ℝ)*X 0 0+(2594865673/5000000000 : ℝ)*X 0 1+(2736571817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645296967/5000000000 : ℝ)*X 1 0+(-1882338087/10000000000 : ℝ)*X 1 1+(1368285897/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645296951/5000000000 : ℝ)*X 2 0+(2736571819/5000000000 : ℝ)*X 2 1+(-1882338061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863255431/2000000000 : ℝ)*X 0 0+(9249597/20000000 : ℝ)*X 0 1+(4027147831/10000000000 : ℝ)*X 0 2+(863255431/2000000000 : ℝ)*X 1 0+(9249597/20000000 : ℝ)*X 1 1+(4027147831/10000000000 : ℝ)*X 1 2+(863255431/2000000000 : ℝ)*X 2 0+(9249597/20000000 : ℝ)*X 2 1+(4027147831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1360_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4285920576593081202788786633/511375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57160987/4000000000000 : ℝ)*(base19) + (1410858173/100000000000000 : ℝ)*(base23) + (28215633/100000000000000 : ℝ)*(lower2) + (195941491/100000000000000 : ℝ)*(upper3) + (29540269/20000000000000 : ℝ)*(upper5) + (1284361621657867/50000000000000 : ℝ)*(major0) + (1284361621657867/50000000000000 : ℝ)*(major1) + (1284361621657867/50000000000000 : ℝ)*(major2) + (1742428603484629/50000000000000 : ℝ)*(sp0) + (3484877223904411/100000000000000 : ℝ)*(sp1) + (3484877242070913/100000000000000 : ℝ)*(sp2) + (413139477961397/25000000000000 : ℝ)*(sp3) + (5361489957/25000000000000 : ℝ)*(sp4) + (9642484473/100000000000000 : ℝ)*(sp7) + (1652567554330061/100000000000000 : ℝ)*(f.failure) + (1742439326464543/50000000000000 : ℝ)*(f.sum) + (14106335059229/61365000000000000000000000000 : ℝ)*base65 + (4837538158831937789/2045500000000000000000000000000000 : ℝ)*base67 + (10522735723975437789/2045500000000000000000000000000000 : ℝ)*base69 + (4385354088929437789/2045500000000000000000000000000000 : ℝ)*base71 + (146344166939063/30682500000000000000000000000 : ℝ)*base74 + (2878945296876937789/2045500000000000000000000000000000 : ℝ)*base75 + (16764337496563937789/2045500000000000000000000000000000 : ℝ)*base77 + (2213058350336062211/2045500000000000000000000000000000 : ℝ)*base80 + (118046318005681/61365000000000000000000000000 : ℝ)*base82 + (91719/125000000000000000000 : ℝ)*base89 + (91719/125000000000000000000 : ℝ)*base91 + (91719/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1939362686929780420926629541/1022750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133057399/25000000000000 : ℝ)*(base19) + (599414079/100000000000000 : ℝ)*(base23) + (54416737/100000000000000 : ℝ)*(upper3) + (16415679/50000000000000 : ℝ)*(lower4) + (4557051/100000000000000 : ℝ)*(upper5) + (1300411391746959/50000000000000 : ℝ)*(major0) + (1300411391746959/50000000000000 : ℝ)*(major1) + (1300411391746959/50000000000000 : ℝ)*(major2) + (373200999/6250000000000 : ℝ)*(sp1) + (1965240169/25000000000000 : ℝ)*(sp2) + (1764213483501957/50000000000000 : ℝ)*(sp4) + (1764210231779167/50000000000000 : ℝ)*(sp5) + (3528418506629159/100000000000000 : ℝ)*(sp6) + (104576158548529/6250000000000 : ℝ)*(sp7) + (104576158548529/6250000000000 : ℝ)*(f.failure) + (1764213483501957/50000000000000 : ℝ)*(f.sum) + (31475833205813/10227500000000000000000000000 : ℝ)*base65 + (958495201715840153/2045500000000000000000000000000000 : ℝ)*base67 + (17713730487412159847/2045500000000000000000000000000000 : ℝ)*base70 + (15820581884787840153/2045500000000000000000000000000000 : ℝ)*base71 + (28905083657977/10227500000000000000000000000 : ℝ)*base74 + (9015567704701840153/2045500000000000000000000000000000 : ℝ)*base75 + (11212107445156840153/2045500000000000000000000000000000 : ℝ)*base77 + (1136570171985159847/2045500000000000000000000000000000 : ℝ)*base80 + (67422427041979/20455000000000000000000000000 : ℝ)*base82 + (15859/7812500000000000000 : ℝ)*base90 + (15859/7812500000000000000 : ℝ)*base92 + (15859/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1360_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (604/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9967/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1360_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1360_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9967/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8017/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1360_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1360_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1360_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4319/1024 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1942979/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9967/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8017/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1360_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
