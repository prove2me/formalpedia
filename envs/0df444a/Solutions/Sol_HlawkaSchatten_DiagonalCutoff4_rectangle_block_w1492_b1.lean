-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1492_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:22.1027+00:00
-- url     : https://prove2.me/submissions/d977743b-1f02-4002-afa1-f89d34fa4a44

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
theorem support_rectangle_w1492_s3_0 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897342573/10000000000 : ℝ)*x 0 + (108799173/200000000 : ℝ)*x 1 + (521286553/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897342573/10000000000 : ℝ)^4481 ≤ (5798222610573/50000000000000 : ℝ)^3457 := by
    have hnat : (1897342573 : ℕ)^4481*50000000000000^3457 ≤ 5798222610573^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897342573 10000000000 5798222610573 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108799173/200000000 : ℝ)^4481 ≤ (45423041981059/100000000000000 : ℝ)^3457 := by
    have hnat : (108799173 : ℕ)^4481*100000000000000^3457 ≤ 45423041981059^3457*200000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108799173 200000000 45423041981059 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521286553/1000000000 : ℝ)^4481 ≤ (268628204893/625000000000 : ℝ)^3457 := by
    have hnat : (521286553 : ℕ)^4481*625000000000^3457 ≤ 268628204893^3457*1000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521286553 1000000000 268628204893 625000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897342573/10000000000 : ℝ), (108799173/200000000 : ℝ), (521286553/1000000000 : ℝ)] ![(5798222610573/50000000000000 : ℝ), (45423041981059/100000000000000 : ℝ), (268628204893/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897342573/10000000000 : ℝ)|^4481 ≤ (5798222610573/50000000000000 : ℝ)^3457
        have hw : |(-1897342573/10000000000 : ℝ)|=(1897342573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108799173/200000000 : ℝ)|^4481 ≤ (45423041981059/100000000000000 : ℝ)^3457
        have hw : |(108799173/200000000 : ℝ)|=(108799173/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521286553/1000000000 : ℝ)|^4481 ≤ (268628204893/625000000000 : ℝ)^3457
        have hw : |(521286553/1000000000 : ℝ)|=(521286553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s3_1 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353750021/10000000000 : ℝ)*x 0 + (-1006897867/5000000000 : ℝ)*x 1 + (651608229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353750021/10000000000 : ℝ)^4481 ≤ (22246092908897/50000000000000 : ℝ)^3457 := by
    have hnat : (5353750021 : ℕ)^4481*50000000000000^3457 ≤ 22246092908897^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353750021 10000000000 22246092908897 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006897867/5000000000 : ℝ)^4481 ≤ (3131824541731/25000000000000 : ℝ)^3457 := by
    have hnat : (1006897867 : ℕ)^4481*25000000000000^3457 ≤ 3131824541731^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006897867 5000000000 3131824541731 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651608229/1250000000 : ℝ)^4481 ≤ (1343141125327/3125000000000 : ℝ)^3457 := by
    have hnat : (651608229 : ℕ)^4481*3125000000000^3457 ≤ 1343141125327^3457*1250000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651608229 1250000000 1343141125327 3125000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353750021/10000000000 : ℝ), (-1006897867/5000000000 : ℝ), (651608229/1250000000 : ℝ)] ![(22246092908897/50000000000000 : ℝ), (3131824541731/25000000000000 : ℝ), (1343141125327/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353750021/10000000000 : ℝ)|^4481 ≤ (22246092908897/50000000000000 : ℝ)^3457
        have hw : |(5353750021/10000000000 : ℝ)|=(5353750021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1006897867/5000000000 : ℝ)|^4481 ≤ (3131824541731/25000000000000 : ℝ)^3457
        have hw : |(-1006897867/5000000000 : ℝ)|=(1006897867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651608229/1250000000 : ℝ)|^4481 ≤ (1343141125327/3125000000000 : ℝ)^3457
        have hw : |(651608229/1250000000 : ℝ)|=(651608229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s3_2 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353749939/10000000000 : ℝ)*x 0 + (2606432881/5000000000 : ℝ)*x 1 + (-402759187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353749939/10000000000 : ℝ)^4481 ≤ (556152311681/1250000000000 : ℝ)^3457 := by
    have hnat : (5353749939 : ℕ)^4481*1250000000000^3457 ≤ 556152311681^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353749939 10000000000 556152311681 1250000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606432881/5000000000 : ℝ)^4481 ≤ (10745128815587/25000000000000 : ℝ)^3457 := by
    have hnat : (2606432881 : ℕ)^4481*25000000000000^3457 ≤ 10745128815587^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606432881 5000000000 10745128815587 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402759187/2000000000 : ℝ)^4481 ≤ (2505459957533/20000000000000 : ℝ)^3457 := by
    have hnat : (402759187 : ℕ)^4481*20000000000000^3457 ≤ 2505459957533^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402759187 2000000000 2505459957533 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353749939/10000000000 : ℝ), (2606432881/5000000000 : ℝ), (-402759187/2000000000 : ℝ)] ![(556152311681/1250000000000 : ℝ), (10745128815587/25000000000000 : ℝ), (2505459957533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353749939/10000000000 : ℝ)|^4481 ≤ (556152311681/1250000000000 : ℝ)^3457
        have hw : |(5353749939/10000000000 : ℝ)|=(5353749939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606432881/5000000000 : ℝ)|^4481 ≤ (10745128815587/25000000000000 : ℝ)^3457
        have hw : |(2606432881/5000000000 : ℝ)|=(2606432881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-402759187/2000000000 : ℝ)|^4481 ≤ (2505459957533/20000000000000 : ℝ)^3457
        have hw : |(-402759187/2000000000 : ℝ)|=(402759187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s3_3 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069696369/2500000000 : ℝ)*x 0 + (1007858683/2500000000 : ℝ)*x 1 + (2269567363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069696369/2500000000 : ℝ)^4481 ≤ (33274669121387/100000000000000 : ℝ)^3457 := by
    have hnat : (1069696369 : ℕ)^4481*100000000000000^3457 ≤ 33274669121387^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069696369 2500000000 33274669121387 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007858683/2500000000 : ℝ)^4481 ≤ (15401485227569/50000000000000 : ℝ)^3457 := by
    have hnat : (1007858683 : ℕ)^4481*50000000000000^3457 ≤ 15401485227569^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007858683 2500000000 15401485227569 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269567363/5000000000 : ℝ)^4481 ≤ (35922360407761/100000000000000 : ℝ)^3457 := by
    have hnat : (2269567363 : ℕ)^4481*100000000000000^3457 ≤ 35922360407761^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269567363 5000000000 35922360407761 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069696369/2500000000 : ℝ), (1007858683/2500000000 : ℝ), (2269567363/5000000000 : ℝ)] ![(33274669121387/100000000000000 : ℝ), (15401485227569/50000000000000 : ℝ), (35922360407761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069696369/2500000000 : ℝ)|^4481 ≤ (33274669121387/100000000000000 : ℝ)^3457
        have hw : |(1069696369/2500000000 : ℝ)|=(1069696369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007858683/2500000000 : ℝ)|^4481 ≤ (15401485227569/50000000000000 : ℝ)^3457
        have hw : |(1007858683/2500000000 : ℝ)|=(1007858683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269567363/5000000000 : ℝ)|^4481 ≤ (35922360407761/100000000000000 : ℝ)^3457
        have hw : |(2269567363/5000000000 : ℝ)|=(2269567363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s3_4 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897375453/10000000000 : ℝ)*x 0 + (1042814347/2000000000 : ℝ)*x 1 + (1359685859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897375453/10000000000 : ℝ)^4481 ≤ (2899176427271/25000000000000 : ℝ)^3457 := by
    have hnat : (1897375453 : ℕ)^4481*25000000000000^3457 ≤ 2899176427271^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897375453 10000000000 2899176427271 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042814347/2000000000 : ℝ)^4481 ≤ (5374175547191/12500000000000 : ℝ)^3457 := by
    have hnat : (1042814347 : ℕ)^4481*12500000000000^3457 ≤ 5374175547191^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042814347 2000000000 5374175547191 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359685859/2500000000 : ℝ)^4481 ≤ (9081977979399/20000000000000 : ℝ)^3457 := by
    have hnat : (1359685859 : ℕ)^4481*20000000000000^3457 ≤ 9081977979399^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359685859 2500000000 9081977979399 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897375453/10000000000 : ℝ), (1042814347/2000000000 : ℝ), (1359685859/2500000000 : ℝ)] ![(2899176427271/25000000000000 : ℝ), (5374175547191/12500000000000 : ℝ), (9081977979399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897375453/10000000000 : ℝ)|^4481 ≤ (2899176427271/25000000000000 : ℝ)^3457
        have hw : |(-1897375453/10000000000 : ℝ)|=(1897375453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042814347/2000000000 : ℝ)|^4481 ≤ (5374175547191/12500000000000 : ℝ)^3457
        have hw : |(1042814347/2000000000 : ℝ)|=(1042814347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359685859/2500000000 : ℝ)|^4481 ≤ (9081977979399/20000000000000 : ℝ)^3457
        have hw : |(1359685859/2500000000 : ℝ)|=(1359685859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s3_5 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323580039/2500000000 : ℝ)*x 0 + (-1787918453/10000000000 : ℝ)*x 1 + (5438743399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323580039/2500000000 : ℝ)^4481 ≤ (43853055385619/100000000000000 : ℝ)^3457 := by
    have hnat : (1323580039 : ℕ)^4481*100000000000000^3457 ≤ 43853055385619^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323580039 2500000000 43853055385619 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1787918453/10000000000 : ℝ)^4481 ≤ (5368527551217/50000000000000 : ℝ)^3457 := by
    have hnat : (1787918453 : ℕ)^4481*50000000000000^3457 ≤ 5368527551217^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787918453 10000000000 5368527551217 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438743399/10000000000 : ℝ)^4481 ≤ (45409889496563/100000000000000 : ℝ)^3457 := by
    have hnat : (5438743399 : ℕ)^4481*100000000000000^3457 ≤ 45409889496563^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438743399 10000000000 45409889496563 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323580039/2500000000 : ℝ), (-1787918453/10000000000 : ℝ), (5438743399/10000000000 : ℝ)] ![(43853055385619/100000000000000 : ℝ), (5368527551217/50000000000000 : ℝ), (45409889496563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323580039/2500000000 : ℝ)|^4481 ≤ (43853055385619/100000000000000 : ℝ)^3457
        have hw : |(1323580039/2500000000 : ℝ)|=(1323580039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1787918453/10000000000 : ℝ)|^4481 ≤ (5368527551217/50000000000000 : ℝ)^3457
        have hw : |(-1787918453/10000000000 : ℝ)|=(1787918453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438743399/10000000000 : ℝ)|^4481 ≤ (45409889496563/100000000000000 : ℝ)^3457
        have hw : |(5438743399/10000000000 : ℝ)|=(5438743399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s3_6 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294320033/10000000000 : ℝ)*x 0 + (2719371751/5000000000 : ℝ)*x 1 + (-22348981/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294320033/10000000000 : ℝ)^4481 ≤ (21926527032511/50000000000000 : ℝ)^3457 := by
    have hnat : (5294320033 : ℕ)^4481*50000000000000^3457 ≤ 21926527032511^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294320033 10000000000 21926527032511 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719371751/5000000000 : ℝ)^4481 ≤ (567623632641/1250000000000 : ℝ)^3457 := by
    have hnat : (2719371751 : ℕ)^4481*1250000000000^3457 ≤ 567623632641^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719371751 5000000000 567623632641 1250000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22348981/125000000 : ℝ)^4481 ≤ (10737055312607/100000000000000 : ℝ)^3457 := by
    have hnat : (22348981 : ℕ)^4481*100000000000000^3457 ≤ 10737055312607^3457*125000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22348981 125000000 10737055312607 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294320033/10000000000 : ℝ), (2719371751/5000000000 : ℝ), (-22348981/125000000 : ℝ)] ![(21926527032511/50000000000000 : ℝ), (567623632641/1250000000000 : ℝ), (10737055312607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294320033/10000000000 : ℝ)|^4481 ≤ (21926527032511/50000000000000 : ℝ)^3457
        have hw : |(5294320033/10000000000 : ℝ)|=(5294320033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719371751/5000000000 : ℝ)|^4481 ≤ (567623632641/1250000000000 : ℝ)^3457
        have hw : |(2719371751/5000000000 : ℝ)|=(2719371751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22348981/125000000 : ℝ)|^4481 ≤ (10737055312607/100000000000000 : ℝ)^3457
        have hw : |(-22348981/125000000 : ℝ)|=(22348981/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s3_7 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855771801/2000000000 : ℝ)*x 0 + (1134110159/2500000000 : ℝ)*x 1 + (4034149807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855771801/2000000000 : ℝ)^4481 ≤ (16637705154849/50000000000000 : ℝ)^3457 := by
    have hnat : (855771801 : ℕ)^4481*50000000000000^3457 ≤ 16637705154849^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855771801 2000000000 16637705154849 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134110159/2500000000 : ℝ)^4481 ≤ (7178945313109/20000000000000 : ℝ)^3457 := by
    have hnat : (1134110159 : ℕ)^4481*20000000000000^3457 ≤ 7178945313109^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134110159 2500000000 7178945313109 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034149807/10000000000 : ℝ)^4481 ≤ (30829863109573/100000000000000 : ℝ)^3457 := by
    have hnat : (4034149807 : ℕ)^4481*100000000000000^3457 ≤ 30829863109573^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034149807 10000000000 30829863109573 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855771801/2000000000 : ℝ), (1134110159/2500000000 : ℝ), (4034149807/10000000000 : ℝ)] ![(16637705154849/50000000000000 : ℝ), (7178945313109/20000000000000 : ℝ), (30829863109573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855771801/2000000000 : ℝ)|^4481 ≤ (16637705154849/50000000000000 : ℝ)^3457
        have hw : |(855771801/2000000000 : ℝ)|=(855771801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134110159/2500000000 : ℝ)|^4481 ≤ (7178945313109/20000000000000 : ℝ)^3457
        have hw : |(1134110159/2500000000 : ℝ)|=(1134110159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034149807/10000000000 : ℝ)|^4481 ≤ (30829863109573/100000000000000 : ℝ)^3457
        have hw : |(4034149807/10000000000 : ℝ)|=(4034149807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1492_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10757/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3891/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5143/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5143/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5143/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5143/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5143/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5143/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5143/50000 : ℝ) ^ (4479/1024 : ℝ) ≤ (956253689080261/20000000000000000000 : ℝ) := by
    have hpowers : (5143/50000 : ℝ)^4479 ≤ (956253689080261/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5143 : ℕ)^4479*20000000000000000000^1024 ≤ 956253689080261^1024*50000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5143 50000 956253689080261 20000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5143/50000 : ℝ)) (X := (956253689080261/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16077/100000 : ℝ) ^ (4479/1024 : ℝ) ≤ (16861341375204191/50000000000000000000 : ℝ) := by
    have hpowers : (16077/100000 : ℝ)^4479 ≤ (16861341375204191/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16077 : ℕ)^4479*50000000000000000000^1024 ≤ 16861341375204191^1024*100000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16077 100000 16861341375204191 50000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16077/100000 : ℝ)) (X := (16861341375204191/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000956253689080261/10000000000000000000 : ℝ) ≤ (1000021861300849/1000000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (10000956253689080261/10000000000000000000 : ℝ)^1024 ≤ (1000021861300849/1000000000000000 : ℝ)^4479 := by
      have hnat : (10000956253689080261 : ℕ)^1024*1000000000000000^4479 ≤ 1000021861300849^4479*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000956253689080261 10000000000000000000 1000021861300849 1000000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021861300849/1000000000000000 : ℝ)) (X := (10000956253689080261/10000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038503951195809687/100000000000000000000 : ℝ) ≤ (10000880156107993/10000000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (100038503951195809687/100000000000000000000 : ℝ)^1024 ≤ (10000880156107993/10000000000000000 : ℝ)^4479 := by
      have hnat : (100038503951195809687 : ℕ)^1024*10000000000000000^4479 ≤ 10000880156107993^4479*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038503951195809687 100000000000000000000 10000880156107993 10000000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000880156107993/10000000000000000 : ℝ)) (X := (100038503951195809687/100000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016861341375204191/25000000000000000000 : ℝ) ≤ (1250192712400937/1250000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (25016861341375204191/25000000000000000000 : ℝ)^1024 ≤ (1250192712400937/1250000000000000 : ℝ)^4479 := by
      have hnat : (25016861341375204191 : ℕ)^1024*1250000000000000^4479 ≤ 1250192712400937^4479*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016861341375204191 25000000000000000000 1250192712400937 1250000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250192712400937/1250000000000000 : ℝ)) (X := (25016861341375204191/25000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(956253689080261/20000000000000000000 : ℝ) ≤ ((28948828361644594937/28955000000000000000 : ℝ)+2*(661543099503/579100000000000 : ℝ)*(5143/50000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (28948828361644594937/28955000000000000000 : ℝ)+2*(661543099503/579100000000000 : ℝ)*(5143/50000 : ℝ)=(1000021861300849/1000000000000000 : ℝ) by norm_num, show 1+2*(956253689080261/20000000000000000000 : ℝ)=(10000956253689080261/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16861341375204191/50000000000000000000 : ℝ)+(956253689080261/20000000000000000000 : ℝ) ≤ ((28948828361644594937/28955000000000000000 : ℝ)+(661543099503/579100000000000 : ℝ)*((16077/100000 : ℝ)+(5143/50000 : ℝ)))^(4479/1024 : ℝ) := by
    rw [show (28948828361644594937/28955000000000000000 : ℝ)+(661543099503/579100000000000 : ℝ)*((16077/100000 : ℝ)+(5143/50000 : ℝ))=(10000880156107993/10000000000000000 : ℝ) by norm_num, show 1+(16861341375204191/50000000000000000000 : ℝ)+(956253689080261/20000000000000000000 : ℝ)=(100038503951195809687/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16861341375204191/50000000000000000000 : ℝ) ≤ ((28948828361644594937/28955000000000000000 : ℝ)+2*(661543099503/579100000000000 : ℝ)*(16077/100000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (28948828361644594937/28955000000000000000 : ℝ)+2*(661543099503/579100000000000 : ℝ)*(16077/100000 : ℝ)=(1250192712400937/1250000000000000 : ℝ) by norm_num, show 1+2*(16861341375204191/50000000000000000000 : ℝ)=(25016861341375204191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28948828361644594937/28955000000000000000 : ℝ)*(X 1 0+X 2 0)+(661543099503/579100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (5143/50000 : ℝ)) (hi := (16077/100000 : ℝ)) (c := (28948828361644594937/28955000000000000000 : ℝ)) (alpha := (661543099503/579100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28948828361644594937/28955000000000000000 : ℝ)*(X 0 1+X 2 1)+(661543099503/579100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (5143/50000 : ℝ)) (hi := (16077/100000 : ℝ)) (c := (28948828361644594937/28955000000000000000 : ℝ)) (alpha := (661543099503/579100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28948828361644594937/28955000000000000000 : ℝ)*(X 0 2+X 1 2)+(661543099503/579100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (5143/50000 : ℝ)) (hi := (16077/100000 : ℝ)) (c := (28948828361644594937/28955000000000000000 : ℝ)) (alpha := (661543099503/579100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1897342573/10000000000 : ℝ)*X 0 0+(108799173/200000000 : ℝ)*X 0 1+(521286553/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353750021/10000000000 : ℝ)*X 1 0+(-1006897867/5000000000 : ℝ)*X 1 1+(651608229/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353749939/10000000000 : ℝ)*X 2 0+(2606432881/5000000000 : ℝ)*X 2 1+(-402759187/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1069696369/2500000000 : ℝ)*X 0 0+(1007858683/2500000000 : ℝ)*X 0 1+(2269567363/5000000000 : ℝ)*X 0 2+(1069696369/2500000000 : ℝ)*X 1 0+(1007858683/2500000000 : ℝ)*X 1 1+(2269567363/5000000000 : ℝ)*X 1 2+(1069696369/2500000000 : ℝ)*X 2 0+(1007858683/2500000000 : ℝ)*X 2 1+(2269567363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1897375453/10000000000 : ℝ)*X 0 0+(1042814347/2000000000 : ℝ)*X 0 1+(1359685859/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323580039/2500000000 : ℝ)*X 1 0+(-1787918453/10000000000 : ℝ)*X 1 1+(5438743399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294320033/10000000000 : ℝ)*X 2 0+(2719371751/5000000000 : ℝ)*X 2 1+(-22348981/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((855771801/2000000000 : ℝ)*X 0 0+(1134110159/2500000000 : ℝ)*X 0 1+(4034149807/10000000000 : ℝ)*X 0 2+(855771801/2000000000 : ℝ)*X 1 0+(1134110159/2500000000 : ℝ)*X 1 1+(4034149807/10000000000 : ℝ)*X 1 2+(855771801/2000000000 : ℝ)*X 2 0+(1134110159/2500000000 : ℝ)*X 2 1+(4034149807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2205460626805999024301227263/361937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (498865091/25000000000000 : ℝ)*(base19) + (459186549/25000000000000 : ℝ)*(base23) + (48862487/100000000000000 : ℝ)*(lower2) + (349475823/100000000000000 : ℝ)*(upper3) + (84649009/100000000000000 : ℝ)*(upper5) + (796654445093533/25000000000000 : ℝ)*(major0) + (796654445093533/25000000000000 : ℝ)*(major1) + (796654445093533/25000000000000 : ℝ)*(major2) + (2201759631542249/50000000000000 : ℝ)*(sp0) + (550443746751807/12500000000000 : ℝ)*(sp1) + (275221883295539/6250000000000 : ℝ)*(sp2) + (1969673796103797/100000000000000 : ℝ)*(sp3) + (32706390323/100000000000000 : ℝ)*(sp4) + (1918410697/20000000000000 : ℝ)*(sp7) + (984841694078641/50000000000000 : ℝ)*(f.failure) + (220177598473741/5000000000000 : ℝ)*(f.sum) + (11427272045747/3619375000000000000000000000 : ℝ)*base65 + (3282401263241682579/723875000000000000000000000000000 : ℝ)*base68 + (3912739898048682579/723875000000000000000000000000000 : ℝ)*base70 + (2811170512687182579/723875000000000000000000000000000 : ℝ)*base72 + (16210073489649/7238750000000000000000000000 : ℝ)*base73 + (3337053811128317421/723875000000000000000000000000000 : ℝ)*base75 + (2361825367032182579/723875000000000000000000000000000 : ℝ)*base78 + (2451308820389192421/723875000000000000000000000000000 : ℝ)*base79 + (139149864740639/28955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2484609/5000000000000000000000 : ℝ)*base89 + (2484609/5000000000000000000000 : ℝ)*base91 + (2484609/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102621339804424408910061/14477500000000000000000000000 : ℝ) := by norm_num
    linear_combination (602629401/50000000000000 : ℝ)*(base19) + (76939451/6250000000000 : ℝ)*(base23) + (153015379/100000000000000 : ℝ)*(upper3) + (29676101/50000000000000 : ℝ)*(lower4) + (12367341/10000000000000 : ℝ)*(upper5) + (1610453740756293/50000000000000 : ℝ)*(major0) + (1610453740756293/50000000000000 : ℝ)*(major1) + (1610453740756293/50000000000000 : ℝ)*(major2) + (2104379087/12500000000000 : ℝ)*(sp1) + (18355979747/100000000000000 : ℝ)*(sp2) + (4450936498363829/100000000000000 : ℝ)*(sp4) + (445091845807233/10000000000000 : ℝ)*(sp5) + (2225458455676433/50000000000000 : ℝ)*(sp6) + (995439114191787/50000000000000 : ℝ)*(sp7) + (995439114191787/50000000000000 : ℝ)*(f.failure) + (4450936498363829/100000000000000 : ℝ)*(f.sum) + (17651557567257/28955000000000000000000000000 : ℝ)*base66 + (8199774294059611459/1447750000000000000000000000000000 : ℝ)*base68 + (3859941393772861459/1447750000000000000000000000000000 : ℝ)*base70 + (11823958106861138541/1447750000000000000000000000000000 : ℝ)*base71 + (38588435188323/7238750000000000000000000000 : ℝ)*base74 + (3495039335797638541/1447750000000000000000000000000000 : ℝ)*base75 + (1672798509919888541/1447750000000000000000000000000000 : ℝ)*base77 + (17686917151339861459/1447750000000000000000000000000000 : ℝ)*base80 + (23572384838057/28955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9975963/5000000000000000000000 : ℝ)*base89 + (9975963/5000000000000000000000 : ℝ)*base91 + (9975963/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1492_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10757/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3891/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1492_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1492_s4_0 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897892231/10000000000 : ℝ)*x 0 + (169886861/312500000 : ℝ)*x 1 + (2608041003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897892231/10000000000 : ℝ)^4481 ≤ (1160079999773/10000000000000 : ℝ)^3457 := by
    have hnat : (1897892231 : ℕ)^4481*10000000000000^3457 ≤ 1160079999773^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897892231 10000000000 1160079999773 10000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169886861/312500000 : ℝ)^4481 ≤ (45384308418449/100000000000000 : ℝ)^3457 := by
    have hnat : (169886861 : ℕ)^4481*100000000000000^3457 ≤ 45384308418449^3457*312500000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169886861 312500000 45384308418449 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608041003/5000000000 : ℝ)^4481 ≤ (43014891576309/100000000000000 : ℝ)^3457 := by
    have hnat : (2608041003 : ℕ)^4481*100000000000000^3457 ≤ 43014891576309^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608041003 5000000000 43014891576309 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897892231/10000000000 : ℝ), (169886861/312500000 : ℝ), (2608041003/5000000000 : ℝ)] ![(1160079999773/10000000000000 : ℝ), (45384308418449/100000000000000 : ℝ), (43014891576309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897892231/10000000000 : ℝ)|^4481 ≤ (1160079999773/10000000000000 : ℝ)^3457
        have hw : |(-1897892231/10000000000 : ℝ)|=(1897892231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169886861/312500000 : ℝ)|^4481 ≤ (45384308418449/100000000000000 : ℝ)^3457
        have hw : |(169886861/312500000 : ℝ)|=(169886861/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608041003/5000000000 : ℝ)|^4481 ≤ (43014891576309/100000000000000 : ℝ)^3457
        have hw : |(2608041003/5000000000 : ℝ)|=(2608041003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s4_1 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338204459/2500000000 : ℝ)*x 0 + (-1005388599/5000000000 : ℝ)*x 1 + (2608041003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338204459/2500000000 : ℝ)^4481 ≤ (11120536116817/25000000000000 : ℝ)^3457 := by
    have hnat : (1338204459 : ℕ)^4481*25000000000000^3457 ≤ 11120536116817^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338204459 2500000000 11120536116817 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005388599/5000000000 : ℝ)^4481 ≤ (12502963945009/100000000000000 : ℝ)^3457 := by
    have hnat : (1005388599 : ℕ)^4481*100000000000000^3457 ≤ 12502963945009^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005388599 5000000000 12502963945009 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608041003/5000000000 : ℝ)^4481 ≤ (43014891576309/100000000000000 : ℝ)^3457 := by
    have hnat : (2608041003 : ℕ)^4481*100000000000000^3457 ≤ 43014891576309^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608041003 5000000000 43014891576309 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338204459/2500000000 : ℝ), (-1005388599/5000000000 : ℝ), (2608041003/5000000000 : ℝ)] ![(11120536116817/25000000000000 : ℝ), (12502963945009/100000000000000 : ℝ), (43014891576309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338204459/2500000000 : ℝ)|^4481 ≤ (11120536116817/25000000000000 : ℝ)^3457
        have hw : |(1338204459/2500000000 : ℝ)|=(1338204459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005388599/5000000000 : ℝ)|^4481 ≤ (12502963945009/100000000000000 : ℝ)^3457
        have hw : |(-1005388599/5000000000 : ℝ)|=(1005388599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608041003/5000000000 : ℝ)|^4481 ≤ (43014891576309/100000000000000 : ℝ)^3457
        have hw : |(2608041003/5000000000 : ℝ)|=(2608041003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s4_2 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338204459/2500000000 : ℝ)*x 0 + (2608041003/5000000000 : ℝ)*x 1 + (-1005388599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338204459/2500000000 : ℝ)^4481 ≤ (11120536116817/25000000000000 : ℝ)^3457 := by
    have hnat : (1338204459 : ℕ)^4481*25000000000000^3457 ≤ 11120536116817^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338204459 2500000000 11120536116817 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608041003/5000000000 : ℝ)^4481 ≤ (43014891576309/100000000000000 : ℝ)^3457 := by
    have hnat : (2608041003 : ℕ)^4481*100000000000000^3457 ≤ 43014891576309^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608041003 5000000000 43014891576309 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005388599/5000000000 : ℝ)^4481 ≤ (12502963945009/100000000000000 : ℝ)^3457 := by
    have hnat : (1005388599 : ℕ)^4481*100000000000000^3457 ≤ 12502963945009^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005388599 5000000000 12502963945009 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338204459/2500000000 : ℝ), (2608041003/5000000000 : ℝ), (-1005388599/5000000000 : ℝ)] ![(11120536116817/25000000000000 : ℝ), (43014891576309/100000000000000 : ℝ), (12502963945009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338204459/2500000000 : ℝ)|^4481 ≤ (11120536116817/25000000000000 : ℝ)^3457
        have hw : |(1338204459/2500000000 : ℝ)|=(1338204459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608041003/5000000000 : ℝ)|^4481 ≤ (43014891576309/100000000000000 : ℝ)^3457
        have hw : |(2608041003/5000000000 : ℝ)|=(2608041003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1005388599/5000000000 : ℝ)|^4481 ≤ (12502963945009/100000000000000 : ℝ)^3457
        have hw : |(-1005388599/5000000000 : ℝ)|=(1005388599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s4_3 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4279127777/10000000000 : ℝ)*x 0 + (1009747309/2500000000 : ℝ)*x 1 + (906300149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279127777/10000000000 : ℝ)^4481 ≤ (8319529905503/25000000000000 : ℝ)^3457 := by
    have hnat : (4279127777 : ℕ)^4481*25000000000000^3457 ≤ 8319529905503^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279127777 10000000000 8319529905503 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009747309/2500000000 : ℝ)^4481 ≤ (7719452664159/25000000000000 : ℝ)^3457 := by
    have hnat : (1009747309 : ℕ)^4481*25000000000000^3457 ≤ 7719452664159^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009747309 2500000000 7719452664159 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906300149/2000000000 : ℝ)^4481 ≤ (35844069703641/100000000000000 : ℝ)^3457 := by
    have hnat : (906300149 : ℕ)^4481*100000000000000^3457 ≤ 35844069703641^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906300149 2000000000 35844069703641 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279127777/10000000000 : ℝ), (1009747309/2500000000 : ℝ), (906300149/2000000000 : ℝ)] ![(8319529905503/25000000000000 : ℝ), (7719452664159/25000000000000 : ℝ), (35844069703641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279127777/10000000000 : ℝ)|^4481 ≤ (8319529905503/25000000000000 : ℝ)^3457
        have hw : |(4279127777/10000000000 : ℝ)|=(4279127777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1009747309/2500000000 : ℝ)|^4481 ≤ (7719452664159/25000000000000 : ℝ)^3457
        have hw : |(1009747309/2500000000 : ℝ)|=(1009747309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906300149/2000000000 : ℝ)|^4481 ≤ (35844069703641/100000000000000 : ℝ)^3457
        have hw : |(906300149/2000000000 : ℝ)|=(906300149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s4_4 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897922459/10000000000 : ℝ)*x 0 + (5217216719/10000000000 : ℝ)*x 1 + (5435236453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897922459/10000000000 : ℝ)^4481 ≤ (11601039496007/100000000000000 : ℝ)^3457 := by
    have hnat : (1897922459 : ℕ)^4481*100000000000000^3457 ≤ 11601039496007^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897922459 10000000000 11601039496007 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217216719/10000000000 : ℝ)^4481 ≤ (43027021274873/100000000000000 : ℝ)^3457 := by
    have hnat : (5217216719 : ℕ)^4481*100000000000000^3457 ≤ 43027021274873^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217216719 10000000000 43027021274873 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435236453/10000000000 : ℝ)^4481 ≤ (22685969606043/50000000000000 : ℝ)^3457 := by
    have hnat : (5435236453 : ℕ)^4481*50000000000000^3457 ≤ 22685969606043^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435236453 10000000000 22685969606043 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897922459/10000000000 : ℝ), (5217216719/10000000000 : ℝ), (5435236453/10000000000 : ℝ)] ![(11601039496007/100000000000000 : ℝ), (43027021274873/100000000000000 : ℝ), (22685969606043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897922459/10000000000 : ℝ)|^4481 ≤ (11601039496007/100000000000000 : ℝ)^3457
        have hw : |(-1897922459/10000000000 : ℝ)|=(1897922459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217216719/10000000000 : ℝ)|^4481 ≤ (43027021274873/100000000000000 : ℝ)^3457
        have hw : |(5217216719/10000000000 : ℝ)|=(5217216719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435236453/10000000000 : ℝ)|^4481 ≤ (22685969606043/50000000000000 : ℝ)^3457
        have hw : |(5435236453/10000000000 : ℝ)|=(5435236453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s4_5 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295168313/10000000000 : ℝ)*x 0 + (-1791622751/10000000000 : ℝ)*x 1 + (5435236453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295168313/10000000000 : ℝ)^4481 ≤ (2193108094579/5000000000000 : ℝ)^3457 := by
    have hnat : (5295168313 : ℕ)^4481*5000000000000^3457 ≤ 2193108094579^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295168313 10000000000 2193108094579 5000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1791622751/10000000000 : ℝ)^4481 ≤ (10765898879859/100000000000000 : ℝ)^3457 := by
    have hnat : (1791622751 : ℕ)^4481*100000000000000^3457 ≤ 10765898879859^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791622751 10000000000 10765898879859 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435236453/10000000000 : ℝ)^4481 ≤ (22685969606043/50000000000000 : ℝ)^3457 := by
    have hnat : (5435236453 : ℕ)^4481*50000000000000^3457 ≤ 22685969606043^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435236453 10000000000 22685969606043 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295168313/10000000000 : ℝ), (-1791622751/10000000000 : ℝ), (5435236453/10000000000 : ℝ)] ![(2193108094579/5000000000000 : ℝ), (10765898879859/100000000000000 : ℝ), (22685969606043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295168313/10000000000 : ℝ)|^4481 ≤ (2193108094579/5000000000000 : ℝ)^3457
        have hw : |(5295168313/10000000000 : ℝ)|=(5295168313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1791622751/10000000000 : ℝ)|^4481 ≤ (10765898879859/100000000000000 : ℝ)^3457
        have hw : |(-1791622751/10000000000 : ℝ)|=(1791622751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435236453/10000000000 : ℝ)|^4481 ≤ (22685969606043/50000000000000 : ℝ)^3457
        have hw : |(5435236453/10000000000 : ℝ)|=(5435236453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s4_6 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295168313/10000000000 : ℝ)*x 0 + (5435236453/10000000000 : ℝ)*x 1 + (-1791622751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295168313/10000000000 : ℝ)^4481 ≤ (2193108094579/5000000000000 : ℝ)^3457 := by
    have hnat : (5295168313 : ℕ)^4481*5000000000000^3457 ≤ 2193108094579^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295168313 10000000000 2193108094579 5000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435236453/10000000000 : ℝ)^4481 ≤ (22685969606043/50000000000000 : ℝ)^3457 := by
    have hnat : (5435236453 : ℕ)^4481*50000000000000^3457 ≤ 22685969606043^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435236453 10000000000 22685969606043 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1791622751/10000000000 : ℝ)^4481 ≤ (10765898879859/100000000000000 : ℝ)^3457 := by
    have hnat : (1791622751 : ℕ)^4481*100000000000000^3457 ≤ 10765898879859^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791622751 10000000000 10765898879859 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295168313/10000000000 : ℝ), (5435236453/10000000000 : ℝ), (-1791622751/10000000000 : ℝ)] ![(2193108094579/5000000000000 : ℝ), (22685969606043/50000000000000 : ℝ), (10765898879859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295168313/10000000000 : ℝ)|^4481 ≤ (2193108094579/5000000000000 : ℝ)^3457
        have hw : |(5295168313/10000000000 : ℝ)|=(5295168313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435236453/10000000000 : ℝ)|^4481 ≤ (22685969606043/50000000000000 : ℝ)^3457
        have hw : |(5435236453/10000000000 : ℝ)|=(5435236453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1791622751/10000000000 : ℝ)|^4481 ≤ (10765898879859/100000000000000 : ℝ)^3457
        have hw : |(-1791622751/10000000000 : ℝ)|=(1791622751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s4_7 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4279195357/10000000000 : ℝ)*x 0 + (2264481953/5000000000 : ℝ)*x 1 + (2020772411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279195357/10000000000 : ℝ)^4481 ≤ (4159850107389/12500000000000 : ℝ)^3457 := by
    have hnat : (4279195357 : ℕ)^4481*12500000000000^3457 ≤ 4159850107389^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279195357 10000000000 4159850107389 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264481953/5000000000 : ℝ)^4481 ≤ (2238628853647/6250000000000 : ℝ)^3457 := by
    have hnat : (2264481953 : ℕ)^4481*6250000000000^3457 ≤ 2238628853647^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264481953 5000000000 2238628853647 6250000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020772411/5000000000 : ℝ)^4481 ≤ (7725784367627/25000000000000 : ℝ)^3457 := by
    have hnat : (2020772411 : ℕ)^4481*25000000000000^3457 ≤ 7725784367627^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020772411 5000000000 7725784367627 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279195357/10000000000 : ℝ), (2264481953/5000000000 : ℝ), (2020772411/5000000000 : ℝ)] ![(4159850107389/12500000000000 : ℝ), (2238628853647/6250000000000 : ℝ), (7725784367627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279195357/10000000000 : ℝ)|^4481 ≤ (4159850107389/12500000000000 : ℝ)^3457
        have hw : |(4279195357/10000000000 : ℝ)|=(4279195357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264481953/5000000000 : ℝ)|^4481 ≤ (2238628853647/6250000000000 : ℝ)^3457
        have hw : |(2264481953/5000000000 : ℝ)|=(2264481953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2020772411/5000000000 : ℝ)|^4481 ≤ (7725784367627/25000000000000 : ℝ)^3457
        have hw : |(2020772411/5000000000 : ℝ)|=(2020772411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1492_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3891/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10757/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5413/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3891/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10757/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3891/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10757/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3891/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10757/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3891/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10757/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3891/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10757/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3891/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10757/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10757/100000 : ℝ) ^ (4479/1024 : ℝ) ≤ (5815599316405091/100000000000000000000 : ℝ) := by
    have hpowers : (10757/100000 : ℝ)^4479 ≤ (5815599316405091/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10757 : ℕ)^4479*100000000000000000000^1024 ≤ 5815599316405091^1024*100000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10757 100000 5815599316405091 100000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10757/100000 : ℝ)) (X := (5815599316405091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3891/25000 : ℝ) ^ (4479/1024 : ℝ) ≤ (14631514946288743/50000000000000000000 : ℝ) := by
    have hpowers : (3891/25000 : ℝ)^4479 ≤ (14631514946288743/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3891 : ℕ)^4479*50000000000000000000^1024 ≤ 14631514946288743^1024*25000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3891 25000 14631514946288743 50000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3891/25000 : ℝ)) (X := (14631514946288743/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005815599316405091/50000000000000000000 : ℝ) ≤ (10000265903396647/10000000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (50005815599316405091/50000000000000000000 : ℝ)^1024 ≤ (10000265903396647/10000000000000000 : ℝ)^4479 := by
      have hnat : (50005815599316405091 : ℕ)^1024*10000000000000000^4479 ≤ 10000265903396647^4479*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005815599316405091 50000000000000000000 10000265903396647 10000000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000265903396647/10000000000000000 : ℝ)) (X := (50005815599316405091/50000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035078629208982577/100000000000000000000 : ℝ) ≤ (2000160373554249/2000000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (100035078629208982577/100000000000000000000 : ℝ)^1024 ≤ (2000160373554249/2000000000000000 : ℝ)^4479 := by
      have hnat : (100035078629208982577 : ℕ)^1024*2000000000000000^4479 ≤ 2000160373554249^4479*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035078629208982577 100000000000000000000 2000160373554249 2000000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000160373554249/2000000000000000 : ℝ)) (X := (100035078629208982577/100000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014631514946288743/25000000000000000000 : ℝ) ≤ (10001337832145843/10000000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (25014631514946288743/25000000000000000000 : ℝ)^1024 ≤ (10001337832145843/10000000000000000 : ℝ)^4479 := by
      have hnat : (25014631514946288743 : ℕ)^1024*10000000000000000^4479 ≤ 10001337832145843^4479*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014631514946288743 25000000000000000000 10001337832145843 10000000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001337832145843/10000000000000000 : ℝ)) (X := (25014631514946288743/25000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5815599316405091/100000000000000000000 : ℝ) ≤ ((48059747460072580757/48070000000000000000 : ℝ)+2*(267982187299/240350000000000 : ℝ)*(10757/100000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (48059747460072580757/48070000000000000000 : ℝ)+2*(267982187299/240350000000000 : ℝ)*(10757/100000 : ℝ)=(10000265903396647/10000000000000000 : ℝ) by norm_num, show 1+2*(5815599316405091/100000000000000000000 : ℝ)=(50005815599316405091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14631514946288743/50000000000000000000 : ℝ)+(5815599316405091/100000000000000000000 : ℝ) ≤ ((48059747460072580757/48070000000000000000 : ℝ)+(267982187299/240350000000000 : ℝ)*((3891/25000 : ℝ)+(10757/100000 : ℝ)))^(4479/1024 : ℝ) := by
    rw [show (48059747460072580757/48070000000000000000 : ℝ)+(267982187299/240350000000000 : ℝ)*((3891/25000 : ℝ)+(10757/100000 : ℝ))=(2000160373554249/2000000000000000 : ℝ) by norm_num, show 1+(14631514946288743/50000000000000000000 : ℝ)+(5815599316405091/100000000000000000000 : ℝ)=(100035078629208982577/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14631514946288743/50000000000000000000 : ℝ) ≤ ((48059747460072580757/48070000000000000000 : ℝ)+2*(267982187299/240350000000000 : ℝ)*(3891/25000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (48059747460072580757/48070000000000000000 : ℝ)+2*(267982187299/240350000000000 : ℝ)*(3891/25000 : ℝ)=(10001337832145843/10000000000000000 : ℝ) by norm_num, show 1+2*(14631514946288743/50000000000000000000 : ℝ)=(25014631514946288743/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (48059747460072580757/48070000000000000000 : ℝ)*(X 1 0+X 2 0)+(267982187299/240350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (10757/100000 : ℝ)) (hi := (3891/25000 : ℝ)) (c := (48059747460072580757/48070000000000000000 : ℝ)) (alpha := (267982187299/240350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (48059747460072580757/48070000000000000000 : ℝ)*(X 0 1+X 2 1)+(267982187299/240350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (10757/100000 : ℝ)) (hi := (3891/25000 : ℝ)) (c := (48059747460072580757/48070000000000000000 : ℝ)) (alpha := (267982187299/240350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (48059747460072580757/48070000000000000000 : ℝ)*(X 0 2+X 1 2)+(267982187299/240350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (10757/100000 : ℝ)) (hi := (3891/25000 : ℝ)) (c := (48059747460072580757/48070000000000000000 : ℝ)) (alpha := (267982187299/240350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1897892231/10000000000 : ℝ)*X 0 0+(169886861/312500000 : ℝ)*X 0 1+(2608041003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338204459/2500000000 : ℝ)*X 1 0+(-1005388599/5000000000 : ℝ)*X 1 1+(2608041003/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338204459/2500000000 : ℝ)*X 2 0+(2608041003/5000000000 : ℝ)*X 2 1+(-1005388599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4279127777/10000000000 : ℝ)*X 0 0+(1009747309/2500000000 : ℝ)*X 0 1+(906300149/2000000000 : ℝ)*X 0 2+(4279127777/10000000000 : ℝ)*X 1 0+(1009747309/2500000000 : ℝ)*X 1 1+(906300149/2000000000 : ℝ)*X 1 2+(4279127777/10000000000 : ℝ)*X 2 0+(1009747309/2500000000 : ℝ)*X 2 1+(906300149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1897922459/10000000000 : ℝ)*X 0 0+(5217216719/10000000000 : ℝ)*X 0 1+(5435236453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295168313/10000000000 : ℝ)*X 1 0+(-1791622751/10000000000 : ℝ)*X 1 1+(5435236453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295168313/10000000000 : ℝ)*X 2 0+(5435236453/10000000000 : ℝ)*X 2 1+(-1791622751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4279195357/10000000000 : ℝ)*X 0 0+(2264481953/5000000000 : ℝ)*X 0 1+(2020772411/5000000000 : ℝ)*X 0 2+(4279195357/10000000000 : ℝ)*X 1 0+(2264481953/5000000000 : ℝ)*X 1 1+(2020772411/5000000000 : ℝ)*X 1 2+(4279195357/10000000000 : ℝ)*X 2 0+(2264481953/5000000000 : ℝ)*X 2 1+(2020772411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (397090021964973159299343879/60087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1175299579/100000000000000 : ℝ)*(base19) + (4284053/390625000000 : ℝ)*(base23) + (42063519/100000000000000 : ℝ)*(lower2) + (165354183/100000000000000 : ℝ)*(upper3) + (21495369/20000000000000 : ℝ)*(upper5) + (164244460326851/5000000000000 : ℝ)*(major0) + (164244460326851/5000000000000 : ℝ)*(major1) + (164244460326851/5000000000000 : ℝ)*(major2) + (4539334048179751/100000000000000 : ℝ)*(sp0) + (453935098337271/10000000000000 : ℝ)*(sp1) + (4539351061954721/100000000000000 : ℝ)*(sp2) + (2030417247027209/100000000000000 : ℝ)*(sp3) + (9055246269/50000000000000 : ℝ)*(sp4) + (1098386277/12500000000000 : ℝ)*(sp7) + (1015213017058713/50000000000000 : ℝ)*(f.failure) + (4539352158672289/100000000000000 : ℝ)*(f.sum) + (518264336291/2403500000000000000000000000 : ℝ)*base66 + (309122961704906207/240350000000000000000000000000000 : ℝ)*base67 + (1590904684755856207/240350000000000000000000000000000 : ℝ)*base69 + (2184932933330056207/240350000000000000000000000000000 : ℝ)*base71 + (585578148061/600875000000000000000000000 : ℝ)*base74 + (2250495257341856207/240350000000000000000000000000000 : ℝ)*base75 + (2168217024421456207/240350000000000000000000000000000 : ℝ)*base77 + (89775346358293793/240350000000000000000000000000000 : ℝ)*base80 + (12289944264899/4807000000000000000000000000 : ℝ)*base81 + (12898537/5000000000000000000000 : ℝ)*base89 + (12898537/5000000000000000000000 : ℝ)*base91 + (12898537/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73230683942313182552331/24035000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20154303/4000000000000 : ℝ)*(base19) + (547190881/100000000000000 : ℝ)*(base23) + (31569077/50000000000000 : ℝ)*(upper3) + (30617/156250000000 : ℝ)*(lower4) + (63090939/100000000000000 : ℝ)*(upper5) + (103724422126657/3125000000000 : ℝ)*(major0) + (103724422126657/3125000000000 : ℝ)*(major1) + (103724422126657/3125000000000 : ℝ)*(major2) + (30455401/400000000000 : ℝ)*(sp1) + (409754629/5000000000000 : ℝ)*(sp2) + (4586740432879279/100000000000000 : ℝ)*(sp4) + (2293366157585727/50000000000000 : ℝ)*(sp5) + (2293365845297909/50000000000000 : ℝ)*(sp6) + (256452810208199/12500000000000 : ℝ)*(sp7) + (256452810208199/12500000000000 : ℝ)*(f.failure) + (4586740432879279/100000000000000 : ℝ)*(f.sum) + (118672933132553/24035000000000000000000000000 : ℝ)*base66 + (574535434111179401/150218750000000000000000000000000 : ℝ)*base68 + (1910573296613633099/150218750000000000000000000000000 : ℝ)*base69 + (330740090919023151/150218750000000000000000000000000 : ℝ)*base72 + (41648432459539/12017500000000000000000000000 : ℝ)*base74 + (384312224194101849/150218750000000000000000000000000 : ℝ)*base75 + (534042842572101849/150218750000000000000000000000000 : ℝ)*base77 + (517092299812148151/150218750000000000000000000000000 : ℝ)*base80 + (8169566177021/12017500000000000000000000000 : ℝ)*base81 + (658551/1250000000000000000000 : ℝ)*base89 + (658551/1250000000000000000000 : ℝ)*base91 + (658551/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1492_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3891/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10757/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5413/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1492_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1492_s5_0 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-379592967/2000000000 : ℝ)*x 0 + (339744171/625000000 : ℝ)*x 1 + (652063353/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379592967/2000000000 : ℝ)^4481 ≤ (11601375245527/100000000000000 : ℝ)^3457 := by
    have hnat : (379592967 : ℕ)^4481*100000000000000^3457 ≤ 11601375245527^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379592967 2000000000 11601375245527 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339744171/625000000 : ℝ)^4481 ≤ (22689596046947/50000000000000 : ℝ)^3457 := by
    have hnat : (339744171 : ℕ)^4481*50000000000000^3457 ≤ 22689596046947^3457*625000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339744171 625000000 22689596046947 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652063353/1250000000 : ℝ)^4481 ≤ (43019432645663/100000000000000 : ℝ)^3457 := by
    have hnat : (652063353 : ℕ)^4481*100000000000000^3457 ≤ 43019432645663^3457*1250000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652063353 1250000000 43019432645663 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379592967/2000000000 : ℝ), (339744171/625000000 : ℝ), (652063353/1250000000 : ℝ)] ![(11601375245527/100000000000000 : ℝ), (22689596046947/50000000000000 : ℝ), (43019432645663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379592967/2000000000 : ℝ)|^4481 ≤ (11601375245527/100000000000000 : ℝ)^3457
        have hw : |(-379592967/2000000000 : ℝ)|=(379592967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339744171/625000000 : ℝ)|^4481 ≤ (22689596046947/50000000000000 : ℝ)^3457
        have hw : |(339744171/625000000 : ℝ)|=(339744171/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652063353/1250000000 : ℝ)|^4481 ≤ (43019432645663/100000000000000 : ℝ)^3457
        have hw : |(652063353/1250000000 : ℝ)|=(652063353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s5_1 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267634717/500000000 : ℝ)*x 0 + (-1005189413/5000000000 : ℝ)*x 1 + (1304126703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267634717/500000000 : ℝ)^4481 ≤ (44480814226591/100000000000000 : ℝ)^3457 := by
    have hnat : (267634717 : ℕ)^4481*100000000000000^3457 ≤ 44480814226591^3457*500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267634717 500000000 44480814226591 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005189413/5000000000 : ℝ)^4481 ≤ (1562469154771/12500000000000 : ℝ)^3457 := by
    have hnat : (1005189413 : ℕ)^4481*12500000000000^3457 ≤ 1562469154771^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005189413 5000000000 1562469154771 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304126703/2500000000 : ℝ)^4481 ≤ (10754858129347/25000000000000 : ℝ)^3457 := by
    have hnat : (1304126703 : ℕ)^4481*25000000000000^3457 ≤ 10754858129347^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304126703 2500000000 10754858129347 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267634717/500000000 : ℝ), (-1005189413/5000000000 : ℝ), (1304126703/2500000000 : ℝ)] ![(44480814226591/100000000000000 : ℝ), (1562469154771/12500000000000 : ℝ), (10754858129347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267634717/500000000 : ℝ)|^4481 ≤ (44480814226591/100000000000000 : ℝ)^3457
        have hw : |(267634717/500000000 : ℝ)|=(267634717/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005189413/5000000000 : ℝ)|^4481 ≤ (1562469154771/12500000000000 : ℝ)^3457
        have hw : |(-1005189413/5000000000 : ℝ)|=(1005189413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304126703/2500000000 : ℝ)|^4481 ≤ (10754858129347/25000000000000 : ℝ)^3457
        have hw : |(1304126703/2500000000 : ℝ)|=(1304126703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s5_2 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352694453/10000000000 : ℝ)*x 0 + (5216506779/10000000000 : ℝ)*x 1 + (-12564867/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352694453/10000000000 : ℝ)^4481 ≤ (44480815443769/100000000000000 : ℝ)^3457 := by
    have hnat : (5352694453 : ℕ)^4481*100000000000000^3457 ≤ 44480815443769^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352694453 10000000000 44480815443769 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216506779/10000000000 : ℝ)^4481 ≤ (5377429020579/12500000000000 : ℝ)^3457 := by
    have hnat : (5216506779 : ℕ)^4481*12500000000000^3457 ≤ 5377429020579^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216506779 10000000000 5377429020579 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12564867/62500000 : ℝ)^4481 ≤ (6249876191939/50000000000000 : ℝ)^3457 := by
    have hnat : (12564867 : ℕ)^4481*50000000000000^3457 ≤ 6249876191939^3457*62500000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12564867 62500000 6249876191939 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352694453/10000000000 : ℝ), (5216506779/10000000000 : ℝ), (-12564867/62500000 : ℝ)] ![(44480815443769/100000000000000 : ℝ), (5377429020579/12500000000000 : ℝ), (6249876191939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352694453/10000000000 : ℝ)|^4481 ≤ (44480815443769/100000000000000 : ℝ)^3457
        have hw : |(5352694453/10000000000 : ℝ)|=(5352694453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216506779/10000000000 : ℝ)|^4481 ≤ (5377429020579/12500000000000 : ℝ)^3457
        have hw : |(5216506779/10000000000 : ℝ)|=(5216506779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12564867/62500000 : ℝ)|^4481 ≤ (6249876191939/50000000000000 : ℝ)^3457
        have hw : |(-12564867/62500000 : ℝ)|=(12564867/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s5_3 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069793079/2500000000 : ℝ)*x 0 + (4039987471/10000000000 : ℝ)*x 1 + (4530492101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069793079/2500000000 : ℝ)^4481 ≤ (33278568595007/100000000000000 : ℝ)^3457 := by
    have hnat : (1069793079 : ℕ)^4481*100000000000000^3457 ≤ 33278568595007^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069793079 2500000000 33278568595007 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4039987471/10000000000 : ℝ)^4481 ≤ (30887702974371/100000000000000 : ℝ)^3457 := by
    have hnat : (4039987471 : ℕ)^4481*100000000000000^3457 ≤ 30887702974371^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039987471 10000000000 30887702974371 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530492101/10000000000 : ℝ)^4481 ≤ (8958432105219/25000000000000 : ℝ)^3457 := by
    have hnat : (4530492101 : ℕ)^4481*25000000000000^3457 ≤ 8958432105219^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530492101 10000000000 8958432105219 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069793079/2500000000 : ℝ), (4039987471/10000000000 : ℝ), (4530492101/10000000000 : ℝ)] ![(33278568595007/100000000000000 : ℝ), (30887702974371/100000000000000 : ℝ), (8958432105219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069793079/2500000000 : ℝ)|^4481 ≤ (33278568595007/100000000000000 : ℝ)^3457
        have hw : |(1069793079/2500000000 : ℝ)|=(1069793079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4039987471/10000000000 : ℝ)|^4481 ≤ (30887702974371/100000000000000 : ℝ)^3457
        have hw : |(4039987471/10000000000 : ℝ)|=(4039987471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530492101/10000000000 : ℝ)|^4481 ≤ (8958432105219/25000000000000 : ℝ)^3457
        have hw : |(4530492101/10000000000 : ℝ)|=(4530492101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s5_4 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-94899737/500000000 : ℝ)*x 0 + (5217632409/10000000000 : ℝ)*x 1 + (1358693209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94899737/500000000 : ℝ)^4481 ≤ (2320322437467/20000000000000 : ℝ)^3457 := by
    have hnat : (94899737 : ℕ)^4481*20000000000000^3457 ≤ 2320322437467^3457*500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94899737 500000000 2320322437467 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217632409/10000000000 : ℝ)^4481 ≤ (43031465056103/100000000000000 : ℝ)^3457 := by
    have hnat : (5217632409 : ℕ)^4481*100000000000000^3457 ≤ 43031465056103^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217632409 10000000000 43031465056103 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358693209/2500000000 : ℝ)^4481 ≤ (9073384548163/20000000000000 : ℝ)^3457 := by
    have hnat : (1358693209 : ℕ)^4481*20000000000000^3457 ≤ 9073384548163^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358693209 2500000000 9073384548163 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94899737/500000000 : ℝ), (5217632409/10000000000 : ℝ), (1358693209/2500000000 : ℝ)] ![(2320322437467/20000000000000 : ℝ), (43031465056103/100000000000000 : ℝ), (9073384548163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94899737/500000000 : ℝ)|^4481 ≤ (2320322437467/20000000000000 : ℝ)^3457
        have hw : |(-94899737/500000000 : ℝ)|=(94899737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217632409/10000000000 : ℝ)|^4481 ≤ (43031465056103/100000000000000 : ℝ)^3457
        have hw : |(5217632409/10000000000 : ℝ)|=(5217632409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358693209/2500000000 : ℝ)|^4481 ≤ (9073384548163/20000000000000 : ℝ)^3457
        have hw : |(1358693209/2500000000 : ℝ)|=(1358693209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s5_5 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295280037/10000000000 : ℝ)*x 0 + (-1792112767/10000000000 : ℝ)*x 1 + (5434772837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295280037/10000000000 : ℝ)^4481 ≤ (43863361483859/100000000000000 : ℝ)^3457 := by
    have hnat : (5295280037 : ℕ)^4481*100000000000000^3457 ≤ 43863361483859^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295280037 10000000000 43863361483859 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1792112767/10000000000 : ℝ)^4481 ≤ (5384857873941/50000000000000 : ℝ)^3457 := by
    have hnat : (1792112767 : ℕ)^4481*50000000000000^3457 ≤ 5384857873941^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792112767 10000000000 5384857873941 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434772837/10000000000 : ℝ)^4481 ≤ (9073384550327/20000000000000 : ℝ)^3457 := by
    have hnat : (5434772837 : ℕ)^4481*20000000000000^3457 ≤ 9073384550327^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434772837 10000000000 9073384550327 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295280037/10000000000 : ℝ), (-1792112767/10000000000 : ℝ), (5434772837/10000000000 : ℝ)] ![(43863361483859/100000000000000 : ℝ), (5384857873941/50000000000000 : ℝ), (9073384550327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295280037/10000000000 : ℝ)|^4481 ≤ (43863361483859/100000000000000 : ℝ)^3457
        have hw : |(5295280037/10000000000 : ℝ)|=(5295280037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1792112767/10000000000 : ℝ)|^4481 ≤ (5384857873941/50000000000000 : ℝ)^3457
        have hw : |(-1792112767/10000000000 : ℝ)|=(1792112767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434772837/10000000000 : ℝ)|^4481 ≤ (9073384550327/20000000000000 : ℝ)^3457
        have hw : |(5434772837/10000000000 : ℝ)|=(5434772837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s5_6 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647640019/5000000000 : ℝ)*x 0 + (5434772837/10000000000 : ℝ)*x 1 + (-896056383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647640019/5000000000 : ℝ)^4481 ≤ (10965840373649/25000000000000 : ℝ)^3457 := by
    have hnat : (2647640019 : ℕ)^4481*25000000000000^3457 ≤ 10965840373649^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647640019 5000000000 10965840373649 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434772837/10000000000 : ℝ)^4481 ≤ (9073384550327/20000000000000 : ℝ)^3457 := by
    have hnat : (5434772837 : ℕ)^4481*20000000000000^3457 ≤ 9073384550327^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434772837 10000000000 9073384550327 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896056383/5000000000 : ℝ)^4481 ≤ (2692428935023/25000000000000 : ℝ)^3457 := by
    have hnat : (896056383 : ℕ)^4481*25000000000000^3457 ≤ 2692428935023^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896056383 5000000000 2692428935023 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647640019/5000000000 : ℝ), (5434772837/10000000000 : ℝ), (-896056383/5000000000 : ℝ)] ![(10965840373649/25000000000000 : ℝ), (9073384550327/20000000000000 : ℝ), (2692428935023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647640019/5000000000 : ℝ)|^4481 ≤ (10965840373649/25000000000000 : ℝ)^3457
        have hw : |(2647640019/5000000000 : ℝ)|=(2647640019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434772837/10000000000 : ℝ)|^4481 ≤ (9073384550327/20000000000000 : ℝ)^3457
        have hw : |(5434772837/10000000000 : ℝ)|=(5434772837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-896056383/5000000000 : ℝ)|^4481 ≤ (2692428935023/25000000000000 : ℝ)^3457
        have hw : |(-896056383/5000000000 : ℝ)|=(896056383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s5_7 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4279239051/10000000000 : ℝ)*x 0 + (905595137/2000000000 : ℝ)*x 1 + (2021261217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279239051/10000000000 : ℝ)^4481 ≤ (33279241316177/100000000000000 : ℝ)^3457 := by
    have hnat : (4279239051 : ℕ)^4481*100000000000000^3457 ≤ 33279241316177^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279239051 10000000000 33279241316177 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905595137/2000000000 : ℝ)^4481 ≤ (8951982859879/25000000000000 : ℝ)^3457 := by
    have hnat : (905595137 : ℕ)^4481*25000000000000^3457 ≤ 8951982859879^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905595137 2000000000 8951982859879 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021261217/5000000000 : ℝ)^4481 ≤ (7728206806509/25000000000000 : ℝ)^3457 := by
    have hnat : (2021261217 : ℕ)^4481*25000000000000^3457 ≤ 7728206806509^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021261217 5000000000 7728206806509 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279239051/10000000000 : ℝ), (905595137/2000000000 : ℝ), (2021261217/5000000000 : ℝ)] ![(33279241316177/100000000000000 : ℝ), (8951982859879/25000000000000 : ℝ), (7728206806509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279239051/10000000000 : ℝ)|^4481 ≤ (33279241316177/100000000000000 : ℝ)^3457
        have hw : |(4279239051/10000000000 : ℝ)|=(4279239051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905595137/2000000000 : ℝ)|^4481 ≤ (8951982859879/25000000000000 : ℝ)^3457
        have hw : |(905595137/2000000000 : ℝ)|=(905595137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2021261217/5000000000 : ℝ)|^4481 ≤ (7728206806509/25000000000000 : ℝ)^3457
        have hw : |(2021261217/5000000000 : ℝ)|=(2021261217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1492_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5413/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2167/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5413/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5413/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5413/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5413/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5413/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5413/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5413/50000 : ℝ) ^ (4479/1024 : ℝ) ≤ (186891919078963/3125000000000000000 : ℝ) := by
    have hpowers : (5413/50000 : ℝ)^4479 ≤ (186891919078963/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5413 : ℕ)^4479*3125000000000000000^1024 ≤ 186891919078963^1024*50000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5413 50000 186891919078963 3125000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5413/50000 : ℝ)) (X := (186891919078963/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4479/1024 : ℝ) ≤ (28651230545371341/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4479 ≤ (28651230545371341/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4479*100000000000000000000^1024 ≤ 28651230545371341^1024*100000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 28651230545371341 100000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (28651230545371341/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562686891919078963/1562500000000000000 : ℝ) ≤ (312508545143873/312500000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (1562686891919078963/1562500000000000000 : ℝ)^1024 ≤ (312508545143873/312500000000000 : ℝ)^4479 := by
      have hnat : (1562686891919078963 : ℕ)^1024*312500000000000^4479 ≤ 312508545143873^4479*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562686891919078963 1562500000000000000 312508545143873 312500000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312508545143873/312500000000000 : ℝ)) (X := (1562686891919078963/1562500000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034631771955898157/100000000000000000000 : ℝ) ≤ (312524739198647/312500000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (100034631771955898157/100000000000000000000 : ℝ)^1024 ≤ (312524739198647/312500000000000 : ℝ)^4479 := by
      have hnat : (100034631771955898157 : ℕ)^1024*312500000000000^4479 ≤ 312524739198647^4479*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034631771955898157 100000000000000000000 312524739198647 312500000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312524739198647/312500000000000 : ℝ)) (X := (100034631771955898157/100000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028651230545371341/50000000000000000000 : ℝ) ≤ (312540933253421/312500000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (50028651230545371341/50000000000000000000 : ℝ)^1024 ≤ (312540933253421/312500000000000 : ℝ)^4479 := by
      have hnat : (50028651230545371341 : ℕ)^1024*312500000000000^4479 ≤ 312540933253421^4479*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028651230545371341 50000000000000000000 312540933253421 312500000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312540933253421/312500000000000 : ℝ)) (X := (50028651230545371341/50000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(186891919078963/3125000000000000000 : ℝ) ≤ ((1456876712331913151/1457187500000000000 : ℝ)+2*(8097027387/7285937500000 : ℝ)*(5413/50000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (1456876712331913151/1457187500000000000 : ℝ)+2*(8097027387/7285937500000 : ℝ)*(5413/50000 : ℝ)=(312508545143873/312500000000000 : ℝ) by norm_num, show 1+2*(186891919078963/3125000000000000000 : ℝ)=(1562686891919078963/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28651230545371341/100000000000000000000 : ℝ)+(186891919078963/3125000000000000000 : ℝ) ≤ ((1456876712331913151/1457187500000000000 : ℝ)+(8097027387/7285937500000 : ℝ)*((15489/100000 : ℝ)+(5413/50000 : ℝ)))^(4479/1024 : ℝ) := by
    rw [show (1456876712331913151/1457187500000000000 : ℝ)+(8097027387/7285937500000 : ℝ)*((15489/100000 : ℝ)+(5413/50000 : ℝ))=(312524739198647/312500000000000 : ℝ) by norm_num, show 1+(28651230545371341/100000000000000000000 : ℝ)+(186891919078963/3125000000000000000 : ℝ)=(100034631771955898157/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28651230545371341/100000000000000000000 : ℝ) ≤ ((1456876712331913151/1457187500000000000 : ℝ)+2*(8097027387/7285937500000 : ℝ)*(15489/100000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (1456876712331913151/1457187500000000000 : ℝ)+2*(8097027387/7285937500000 : ℝ)*(15489/100000 : ℝ)=(312540933253421/312500000000000 : ℝ) by norm_num, show 1+2*(28651230545371341/100000000000000000000 : ℝ)=(50028651230545371341/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1456876712331913151/1457187500000000000 : ℝ)*(X 1 0+X 2 0)+(8097027387/7285937500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (5413/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1456876712331913151/1457187500000000000 : ℝ)) (alpha := (8097027387/7285937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1456876712331913151/1457187500000000000 : ℝ)*(X 0 1+X 2 1)+(8097027387/7285937500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (5413/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1456876712331913151/1457187500000000000 : ℝ)) (alpha := (8097027387/7285937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1456876712331913151/1457187500000000000 : ℝ)*(X 0 2+X 1 2)+(8097027387/7285937500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (5413/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1456876712331913151/1457187500000000000 : ℝ)) (alpha := (8097027387/7285937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-379592967/2000000000 : ℝ)*X 0 0+(339744171/625000000 : ℝ)*X 0 1+(652063353/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267634717/500000000 : ℝ)*X 1 0+(-1005189413/5000000000 : ℝ)*X 1 1+(1304126703/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352694453/10000000000 : ℝ)*X 2 0+(5216506779/10000000000 : ℝ)*X 2 1+(-12564867/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1069793079/2500000000 : ℝ)*X 0 0+(4039987471/10000000000 : ℝ)*X 0 1+(4530492101/10000000000 : ℝ)*X 0 2+(1069793079/2500000000 : ℝ)*X 1 0+(4039987471/10000000000 : ℝ)*X 1 1+(4530492101/10000000000 : ℝ)*X 1 2+(1069793079/2500000000 : ℝ)*X 2 0+(4039987471/10000000000 : ℝ)*X 2 1+(4530492101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-94899737/500000000 : ℝ)*X 0 0+(5217632409/10000000000 : ℝ)*X 0 1+(1358693209/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295280037/10000000000 : ℝ)*X 1 0+(-1792112767/10000000000 : ℝ)*X 1 1+(5434772837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647640019/5000000000 : ℝ)*X 2 0+(5434772837/10000000000 : ℝ)*X 2 1+(-896056383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4279239051/10000000000 : ℝ)*X 0 0+(905595137/2000000000 : ℝ)*X 0 1+(2021261217/5000000000 : ℝ)*X 0 2+(4279239051/10000000000 : ℝ)*X 1 0+(905595137/2000000000 : ℝ)*X 1 1+(2021261217/5000000000 : ℝ)*X 1 2+(4279239051/10000000000 : ℝ)*X 2 0+(905595137/2000000000 : ℝ)*X 2 1+(2021261217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (549140967975938348057524689/72859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1340490147/100000000000000 : ℝ)*(base19) + (1300693077/100000000000000 : ℝ)*(base23) + (72806747/100000000000000 : ℝ)*(lower2) + (28087333/20000000000000 : ℝ)*(upper3) + (157141373/100000000000000 : ℝ)*(upper5) + (412291611348593/12500000000000 : ℝ)*(major0) + (412291611348593/12500000000000 : ℝ)*(major1) + (412291611348593/12500000000000 : ℝ)*(major2) + (569738389293869/12500000000000 : ℝ)*(sp0) + (4557928467103969/100000000000000 : ℝ)*(sp1) + (2278964253450519/50000000000000 : ℝ)*(sp2) + (2038725940113313/100000000000000 : ℝ)*(sp3) + (22693243163/100000000000000 : ℝ)*(sp4) + (9782636787/100000000000000 : ℝ)*(sp7) + (20387357227501/1000000000000 : ℝ)*(f.failure) + (911585961518823/20000000000000 : ℝ)*(f.sum) + (6976632470683/23315000000000000000000000000 : ℝ)*base66 + (31798044190123203/72859375000000000000000000000000 : ℝ)*base68 + (195668179610279453/72859375000000000000000000000000 : ℝ)*base70 + (640337004793623203/72859375000000000000000000000000 : ℝ)*base72 + (28377722469333/5828750000000000000000000000 : ℝ)*base73 + (177214365270529453/72859375000000000000000000000000 : ℝ)*base76 + (441045248448341953/72859375000000000000000000000000 : ℝ)*base78 + (25240588841652793/18214843750000000000000000000000 : ℝ)*base79 + (73634970685073/23315000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (69251/100000000000000000000 : ℝ)*base90 + (69251/100000000000000000000 : ℝ)*base92 + (69251/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (871897275260886859262322639/72859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (246365441/12500000000000 : ℝ)*(base19) + (106999253/5000000000000 : ℝ)*(base23) + (653012961/100000000000000 : ℝ)*(lower1) + (247218937/100000000000000 : ℝ)*(upper3) + (2370333/3125000000000 : ℝ)*(lower4) + (61590761/25000000000000 : ℝ)*(upper5) + (1666300123560903/50000000000000 : ℝ)*(major0) + (1666300123560903/50000000000000 : ℝ)*(major1) + (1666300123560903/50000000000000 : ℝ)*(major2) + (230110077/10000000000000 : ℝ)*(sp2) + (4605283343941373/100000000000000 : ℝ)*(sp4) + (921056274603569/20000000000000 : ℝ)*(sp5) + (4605278902855543/100000000000000 : ℝ)*(sp6) + (205991675140719/10000000000000 : ℝ)*(sp7) + (205991675140719/10000000000000 : ℝ)*(f.failure) + (4605283343941373/100000000000000 : ℝ)*(f.sum) + (45327857833979/11657500000000000000000000000 : ℝ)*base65 + (132467862378560693/18214843750000000000000000000000 : ℝ)*base68 + (837027869201335353/72859375000000000000000000000000 : ℝ)*base69 + (825516266494783057/18214843750000000000000000000000 : ℝ)*base71 + (65159580277017/23315000000000000000000000000 : ℝ)*base74 + (2984426863087144239/36429687500000000000000000000000 : ℝ)*base75 + (362530326421679103/72859375000000000000000000000000 : ℝ)*base77 + (452476544650663/284606933593750000000000000000 : ℝ)*base79 + (1398603877289/11657500000000000000000000000 : ℝ)*base81 + (7983969/1000000000000000000000 : ℝ)*base90 + (7983969/1000000000000000000000 : ℝ)*base92 + (7983969/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1492_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5413/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2167/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1492_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1492_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2167/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1492_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1492_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1492_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5143/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2167/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1492_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
