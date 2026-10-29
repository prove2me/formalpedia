-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1363_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:42.282673+00:00
-- url     : https://prove2.me/submissions/46421371-a93a-4574-821e-3c3ddad2b9a6

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
theorem support_rectangle_w1363_s3_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-506102697/2500000000 : ℝ)*x 0 + (5424558953/10000000000 : ℝ)*x 1 + (5233318231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506102697/2500000000 : ℝ)^4323 ≤ (6165180054959/50000000000000 : ℝ)^3299 := by
    have hnat : (506102697 : ℕ)^4323*50000000000000^3299 ≤ 6165180054959^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506102697 2500000000 6165180054959 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424558953/10000000000 : ℝ)^4323 ≤ (22432719753107/50000000000000 : ℝ)^3299 := by
    have hnat : (5424558953 : ℕ)^4323*50000000000000^3299 ≤ 22432719753107^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424558953 10000000000 22432719753107 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233318231/10000000000 : ℝ)^4323 ≤ (42804200371641/100000000000000 : ℝ)^3299 := by
    have hnat : (5233318231 : ℕ)^4323*100000000000000^3299 ≤ 42804200371641^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233318231 10000000000 42804200371641 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506102697/2500000000 : ℝ), (5424558953/10000000000 : ℝ), (5233318231/10000000000 : ℝ)] ![(6165180054959/50000000000000 : ℝ), (22432719753107/50000000000000 : ℝ), (42804200371641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506102697/2500000000 : ℝ)|^4323 ≤ (6165180054959/50000000000000 : ℝ)^3299
        have hw : |(-506102697/2500000000 : ℝ)|=(506102697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424558953/10000000000 : ℝ)|^4323 ≤ (22432719753107/50000000000000 : ℝ)^3299
        have hw : |(5424558953/10000000000 : ℝ)|=(5424558953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233318231/10000000000 : ℝ)|^4323 ≤ (42804200371641/100000000000000 : ℝ)^3299
        have hw : |(5233318231/10000000000 : ℝ)|=(5233318231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s3_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351934301/10000000000 : ℝ)*x 0 + (-530524747/2500000000 : ℝ)*x 1 + (523331839/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351934301/10000000000 : ℝ)^4323 ≤ (11019992940321/25000000000000 : ℝ)^3299 := by
    have hnat : (5351934301 : ℕ)^4323*25000000000000^3299 ≤ 11019992940321^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351934301 10000000000 11019992940321 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530524747/2500000000 : ℝ)^4323 ≤ (13115826149751/100000000000000 : ℝ)^3299 := by
    have hnat : (530524747 : ℕ)^4323*100000000000000^3299 ≤ 13115826149751^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530524747 2500000000 13115826149751 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523331839/1000000000 : ℝ)^4323 ≤ (42804202075797/100000000000000 : ℝ)^3299 := by
    have hnat : (523331839 : ℕ)^4323*100000000000000^3299 ≤ 42804202075797^3299*1000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523331839 1000000000 42804202075797 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351934301/10000000000 : ℝ), (-530524747/2500000000 : ℝ), (523331839/1000000000 : ℝ)] ![(11019992940321/25000000000000 : ℝ), (13115826149751/100000000000000 : ℝ), (42804202075797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351934301/10000000000 : ℝ)|^4323 ≤ (11019992940321/25000000000000 : ℝ)^3299
        have hw : |(5351934301/10000000000 : ℝ)|=(5351934301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-530524747/2500000000 : ℝ)|^4323 ≤ (13115826149751/100000000000000 : ℝ)^3299
        have hw : |(-530524747/2500000000 : ℝ)|=(530524747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523331839/1000000000 : ℝ)|^4323 ≤ (42804202075797/100000000000000 : ℝ)^3299
        have hw : |(523331839/1000000000 : ℝ)|=(523331839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s3_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351934823/10000000000 : ℝ)*x 0 + (1046663591/2000000000 : ℝ)*x 1 + (-2122098867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351934823/10000000000 : ℝ)^4323 ≤ (44079977395117/100000000000000 : ℝ)^3299 := by
    have hnat : (5351934823 : ℕ)^4323*100000000000000^3299 ≤ 44079977395117^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351934823 10000000000 44079977395117 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046663591/2000000000 : ℝ)^4323 ≤ (10701049353371/25000000000000 : ℝ)^3299 := by
    have hnat : (1046663591 : ℕ)^4323*25000000000000^3299 ≤ 10701049353371^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046663591 2000000000 10701049353371 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122098867/10000000000 : ℝ)^4323 ≤ (1639478146221/12500000000000 : ℝ)^3299 := by
    have hnat : (2122098867 : ℕ)^4323*12500000000000^3299 ≤ 1639478146221^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122098867 10000000000 1639478146221 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351934823/10000000000 : ℝ), (1046663591/2000000000 : ℝ), (-2122098867/10000000000 : ℝ)] ![(44079977395117/100000000000000 : ℝ), (10701049353371/25000000000000 : ℝ), (1639478146221/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351934823/10000000000 : ℝ)|^4323 ≤ (44079977395117/100000000000000 : ℝ)^3299
        have hw : |(5351934823/10000000000 : ℝ)|=(5351934823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046663591/2000000000 : ℝ)|^4323 ≤ (10701049353371/25000000000000 : ℝ)^3299
        have hw : |(1046663591/2000000000 : ℝ)|=(1046663591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122098867/10000000000 : ℝ)|^4323 ≤ (1639478146221/12500000000000 : ℝ)^3299
        have hw : |(-2122098867/10000000000 : ℝ)|=(2122098867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s3_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320215833/10000000000 : ℝ)*x 0 + (824542133/2000000000 : ℝ)*x 1 + (4526445587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320215833/10000000000 : ℝ)^4323 ≤ (16647054413509/50000000000000 : ℝ)^3299 := by
    have hnat : (4320215833 : ℕ)^4323*50000000000000^3299 ≤ 16647054413509^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320215833 10000000000 16647054413509 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824542133/2000000000 : ℝ)^4323 ≤ (15656934676641/50000000000000 : ℝ)^3299 := by
    have hnat : (824542133 : ℕ)^4323*50000000000000^3299 ≤ 15656934676641^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824542133 2000000000 15656934676641 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526445587/10000000000 : ℝ)^4323 ≤ (17696010905601/50000000000000 : ℝ)^3299 := by
    have hnat : (4526445587 : ℕ)^4323*50000000000000^3299 ≤ 17696010905601^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526445587 10000000000 17696010905601 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320215833/10000000000 : ℝ), (824542133/2000000000 : ℝ), (4526445587/10000000000 : ℝ)] ![(16647054413509/50000000000000 : ℝ), (15656934676641/50000000000000 : ℝ), (17696010905601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320215833/10000000000 : ℝ)|^4323 ≤ (16647054413509/50000000000000 : ℝ)^3299
        have hw : |(4320215833/10000000000 : ℝ)|=(4320215833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824542133/2000000000 : ℝ)|^4323 ≤ (15656934676641/50000000000000 : ℝ)^3299
        have hw : |(824542133/2000000000 : ℝ)|=(824542133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526445587/10000000000 : ℝ)|^4323 ≤ (17696010905601/50000000000000 : ℝ)^3299
        have hw : |(4526445587/10000000000 : ℝ)|=(4526445587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s3_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-202442949/1000000000 : ℝ)*x 0 + (5234105639/10000000000 : ℝ)*x 1 + (271188323/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202442949/1000000000 : ℝ)^4323 ≤ (2466101875721/20000000000000 : ℝ)^3299 := by
    have hnat : (202442949 : ℕ)^4323*20000000000000^3299 ≤ 2466101875721^3299*1000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202442949 1000000000 2466101875721 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234105639/10000000000 : ℝ)^4323 ≤ (5351579997097/12500000000000 : ℝ)^3299 := by
    have hnat : (5234105639 : ℕ)^4323*12500000000000^3299 ≤ 5351579997097^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234105639 10000000000 5351579997097 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271188323/500000000 : ℝ)^4323 ≤ (8971370127357/20000000000000 : ℝ)^3299 := by
    have hnat : (271188323 : ℕ)^4323*20000000000000^3299 ≤ 8971370127357^3299*500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271188323 500000000 8971370127357 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202442949/1000000000 : ℝ), (5234105639/10000000000 : ℝ), (271188323/500000000 : ℝ)] ![(2466101875721/20000000000000 : ℝ), (5351579997097/12500000000000 : ℝ), (8971370127357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202442949/1000000000 : ℝ)|^4323 ≤ (2466101875721/20000000000000 : ℝ)^3299
        have hw : |(-202442949/1000000000 : ℝ)|=(202442949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234105639/10000000000 : ℝ)|^4323 ≤ (5351579997097/12500000000000 : ℝ)^3299
        have hw : |(5234105639/10000000000 : ℝ)|=(5234105639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271188323/500000000 : ℝ)|^4323 ≤ (8971370127357/20000000000000 : ℝ)^3299
        have hw : |(271188323/500000000 : ℝ)|=(271188323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s3_5 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651278711/5000000000 : ℝ)*x 0 + (-1931650451/10000000000 : ℝ)*x 1 + (5423766851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651278711/5000000000 : ℝ)^4323 ≤ (21773911246391/50000000000000 : ℝ)^3299 := by
    have hnat : (2651278711 : ℕ)^4323*50000000000000^3299 ≤ 21773911246391^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651278711 5000000000 21773911246391 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931650451/10000000000 : ℝ)^4323 ≤ (11595322616223/100000000000000 : ℝ)^3299 := by
    have hnat : (1931650451 : ℕ)^4323*100000000000000^3299 ≤ 11595322616223^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931650451 10000000000 11595322616223 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423766851/10000000000 : ℝ)^4323 ≤ (44856854874263/100000000000000 : ℝ)^3299 := by
    have hnat : (5423766851 : ℕ)^4323*100000000000000^3299 ≤ 44856854874263^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423766851 10000000000 44856854874263 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651278711/5000000000 : ℝ), (-1931650451/10000000000 : ℝ), (5423766851/10000000000 : ℝ)] ![(21773911246391/50000000000000 : ℝ), (11595322616223/100000000000000 : ℝ), (44856854874263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651278711/5000000000 : ℝ)|^4323 ≤ (21773911246391/50000000000000 : ℝ)^3299
        have hw : |(2651278711/5000000000 : ℝ)|=(2651278711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1931650451/10000000000 : ℝ)|^4323 ≤ (11595322616223/100000000000000 : ℝ)^3299
        have hw : |(-1931650451/10000000000 : ℝ)|=(1931650451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423766851/10000000000 : ℝ)|^4323 ≤ (44856854874263/100000000000000 : ℝ)^3299
        have hw : |(5423766851/10000000000 : ℝ)|=(5423766851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s3_6 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302558209/10000000000 : ℝ)*x 0 + (1355941577/2500000000 : ℝ)*x 1 + (-965825061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302558209/10000000000 : ℝ)^4323 ≤ (435478309623/1000000000000 : ℝ)^3299 := by
    have hnat : (5302558209 : ℕ)^4323*1000000000000^3299 ≤ 435478309623^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302558209 10000000000 435478309623 1000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355941577/2500000000 : ℝ)^4323 ≤ (44856848989479/100000000000000 : ℝ)^3299 := by
    have hnat : (1355941577 : ℕ)^4323*100000000000000^3299 ≤ 44856848989479^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355941577 2500000000 44856848989479 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965825061/5000000000 : ℝ)^4323 ≤ (11595320028289/100000000000000 : ℝ)^3299 := by
    have hnat : (965825061 : ℕ)^4323*100000000000000^3299 ≤ 11595320028289^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965825061 5000000000 11595320028289 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302558209/10000000000 : ℝ), (1355941577/2500000000 : ℝ), (-965825061/5000000000 : ℝ)] ![(435478309623/1000000000000 : ℝ), (44856848989479/100000000000000 : ℝ), (11595320028289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302558209/10000000000 : ℝ)|^4323 ≤ (435478309623/1000000000000 : ℝ)^3299
        have hw : |(5302558209/10000000000 : ℝ)|=(5302558209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355941577/2500000000 : ℝ)|^4323 ≤ (44856848989479/100000000000000 : ℝ)^3299
        have hw : |(1355941577/2500000000 : ℝ)|=(1355941577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-965825061/5000000000 : ℝ)|^4323 ≤ (11595320028289/100000000000000 : ℝ)^3299
        have hw : |(-965825061/5000000000 : ℝ)|=(965825061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s3_7 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320253521/10000000000 : ℝ)*x 0 + (904956639/2000000000 : ℝ)*x 1 + (4124383529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320253521/10000000000 : ℝ)^4323 ≤ (8323622356703/25000000000000 : ℝ)^3299 := by
    have hnat : (4320253521 : ℕ)^4323*25000000000000^3299 ≤ 8323622356703^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320253521 10000000000 8323622356703 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904956639/2000000000 : ℝ)^4323 ≤ (1414999601823/4000000000000 : ℝ)^3299 := by
    have hnat : (904956639 : ℕ)^4323*4000000000000^3299 ≤ 1414999601823^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904956639 2000000000 1414999601823 4000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4124383529/10000000000 : ℝ)^4323 ≤ (6266104104849/20000000000000 : ℝ)^3299 := by
    have hnat : (4124383529 : ℕ)^4323*20000000000000^3299 ≤ 6266104104849^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124383529 10000000000 6266104104849 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320253521/10000000000 : ℝ), (904956639/2000000000 : ℝ), (4124383529/10000000000 : ℝ)] ![(8323622356703/25000000000000 : ℝ), (1414999601823/4000000000000 : ℝ), (6266104104849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320253521/10000000000 : ℝ)|^4323 ≤ (8323622356703/25000000000000 : ℝ)^3299
        have hw : |(4320253521/10000000000 : ℝ)|=(4320253521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904956639/2000000000 : ℝ)|^4323 ≤ (1414999601823/4000000000000 : ℝ)^3299
        have hw : |(904956639/2000000000 : ℝ)|=(904956639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4124383529/10000000000 : ℝ)|^4323 ≤ (6266104104849/20000000000000 : ℝ)^3299
        have hw : |(4124383529/10000000000 : ℝ)|=(4124383529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10943/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14991/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4993/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4993/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4993/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4993/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4993/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4993/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4993/50000 : ℝ) ^ (2161/512 : ℝ) ≤ (5980380788029059/100000000000000000000 : ℝ) := by
    have hpowers : (4993/50000 : ℝ)^2161 ≤ (5980380788029059/100000000000000000000 : ℝ)^512 := by
      have hnat : (4993 : ℕ)^2161*100000000000000000000^512 ≤ 5980380788029059^512*50000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4993 50000 5980380788029059 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4993/50000 : ℝ)) (X := (5980380788029059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16023/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (11000180668404949/25000000000000000000 : ℝ) := by
    have hpowers : (16023/100000 : ℝ)^2161 ≤ (11000180668404949/25000000000000000000 : ℝ)^512 := by
      have hnat : (16023 : ℕ)^2161*25000000000000000000^512 ≤ 11000180668404949^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16023 100000 11000180668404949 25000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16023/100000 : ℝ)) (X := (11000180668404949/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005980380788029059/50000000000000000000 : ℝ) ≤ (1250035421277673/1250000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50005980380788029059/50000000000000000000 : ℝ)^512 ≤ (1250035421277673/1250000000000000 : ℝ)^2161 := by
      have hnat : (50005980380788029059 : ℕ)^512*1250000000000000^2161 ≤ 1250035421277673^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005980380788029059 50000000000000000000 1250035421277673 1250000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035421277673/1250000000000000 : ℝ)) (X := (50005980380788029059/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009996220692329771/20000000000000000000 : ℝ) ≤ (78134249713107/78125000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (20009996220692329771/20000000000000000000 : ℝ)^512 ≤ (78134249713107/78125000000000 : ℝ)^2161 := by
      have hnat : (20009996220692329771 : ℕ)^512*78125000000000^2161 ≤ 78134249713107^2161*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009996220692329771 20000000000000000000 78134249713107 78125000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78134249713107/78125000000000 : ℝ)) (X := (20009996220692329771/20000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511000180668404949/12500000000000000000 : ℝ) ≤ (1250260569541751/1250000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (12511000180668404949/12500000000000000000 : ℝ)^512 ≤ (1250260569541751/1250000000000000 : ℝ)^2161 := by
      have hnat : (12511000180668404949 : ℕ)^512*1250000000000000^2161 ≤ 1250260569541751^2161*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511000180668404949 12500000000000000000 1250260569541751 1250000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250260569541751/1250000000000000 : ℝ)) (X := (12511000180668404949/12500000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5980380788029059/100000000000000000000 : ℝ) ≤ ((7544215507688228993/7546250000000000000 : ℝ)+2*(112574132039/75462500000000 : ℝ)*(4993/50000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (7544215507688228993/7546250000000000000 : ℝ)+2*(112574132039/75462500000000 : ℝ)*(4993/50000 : ℝ)=(1250035421277673/1250000000000000 : ℝ) by norm_num, show 1+2*(5980380788029059/100000000000000000000 : ℝ)=(50005980380788029059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11000180668404949/25000000000000000000 : ℝ)+(5980380788029059/100000000000000000000 : ℝ) ≤ ((7544215507688228993/7546250000000000000 : ℝ)+(112574132039/75462500000000 : ℝ)*((16023/100000 : ℝ)+(4993/50000 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (7544215507688228993/7546250000000000000 : ℝ)+(112574132039/75462500000000 : ℝ)*((16023/100000 : ℝ)+(4993/50000 : ℝ))=(78134249713107/78125000000000 : ℝ) by norm_num, show 1+(11000180668404949/25000000000000000000 : ℝ)+(5980380788029059/100000000000000000000 : ℝ)=(20009996220692329771/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11000180668404949/25000000000000000000 : ℝ) ≤ ((7544215507688228993/7546250000000000000 : ℝ)+2*(112574132039/75462500000000 : ℝ)*(16023/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (7544215507688228993/7546250000000000000 : ℝ)+2*(112574132039/75462500000000 : ℝ)*(16023/100000 : ℝ)=(1250260569541751/1250000000000000 : ℝ) by norm_num, show 1+2*(11000180668404949/25000000000000000000 : ℝ)=(12511000180668404949/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7544215507688228993/7546250000000000000 : ℝ)*(X 1 0+X 2 0)+(112574132039/75462500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (4993/50000 : ℝ)) (hi := (16023/100000 : ℝ)) (c := (7544215507688228993/7546250000000000000 : ℝ)) (alpha := (112574132039/75462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7544215507688228993/7546250000000000000 : ℝ)*(X 0 1+X 2 1)+(112574132039/75462500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (4993/50000 : ℝ)) (hi := (16023/100000 : ℝ)) (c := (7544215507688228993/7546250000000000000 : ℝ)) (alpha := (112574132039/75462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7544215507688228993/7546250000000000000 : ℝ)*(X 0 2+X 1 2)+(112574132039/75462500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (4993/50000 : ℝ)) (hi := (16023/100000 : ℝ)) (c := (7544215507688228993/7546250000000000000 : ℝ)) (alpha := (112574132039/75462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-506102697/2500000000 : ℝ)*X 0 0+(5424558953/10000000000 : ℝ)*X 0 1+(5233318231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351934301/10000000000 : ℝ)*X 1 0+(-530524747/2500000000 : ℝ)*X 1 1+(523331839/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351934823/10000000000 : ℝ)*X 2 0+(1046663591/2000000000 : ℝ)*X 2 1+(-2122098867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320215833/10000000000 : ℝ)*X 0 0+(824542133/2000000000 : ℝ)*X 0 1+(4526445587/10000000000 : ℝ)*X 0 2+(4320215833/10000000000 : ℝ)*X 1 0+(824542133/2000000000 : ℝ)*X 1 1+(4526445587/10000000000 : ℝ)*X 1 2+(4320215833/10000000000 : ℝ)*X 2 0+(824542133/2000000000 : ℝ)*X 2 1+(4526445587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-202442949/1000000000 : ℝ)*X 0 0+(5234105639/10000000000 : ℝ)*X 0 1+(271188323/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651278711/5000000000 : ℝ)*X 1 0+(-1931650451/10000000000 : ℝ)*X 1 1+(5423766851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302558209/10000000000 : ℝ)*X 2 0+(1355941577/2500000000 : ℝ)*X 2 1+(-965825061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320253521/10000000000 : ℝ)*X 0 0+(904956639/2000000000 : ℝ)*X 0 1+(4124383529/10000000000 : ℝ)*X 0 2+(4320253521/10000000000 : ℝ)*X 1 0+(904956639/2000000000 : ℝ)*X 1 1+(4124383529/10000000000 : ℝ)*X 1 2+(4320253521/10000000000 : ℝ)*X 2 0+(904956639/2000000000 : ℝ)*X 2 1+(4124383529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (288245001986008020393297351/47164062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (730886781/50000000000000 : ℝ)*(base19) + (1095589321/100000000000000 : ℝ)*(base23) + (136905649/25000000000000 : ℝ)*(lower2) + (440144903/100000000000000 : ℝ)*(upper3) + (19671719/25000000000000 : ℝ)*(lower4) + (1926485310958837/50000000000000 : ℝ)*(major0) + (1926485310958837/50000000000000 : ℝ)*(major1) + (1926485310958837/50000000000000 : ℝ)*(major2) + (5229031529488739/100000000000000 : ℝ)*(sp0) + (1307261977168447/25000000000000 : ℝ)*(sp1) + (5229048274858029/100000000000000 : ℝ)*(sp2) + (2476876843617871/100000000000000 : ℝ)*(sp3) + (1784095861/10000000000000 : ℝ)*(sp4) + (14826052153/100000000000000 : ℝ)*(sp7) + (309611458708753/12500000000000 : ℝ)*(f.failure) + (104580987408947/2000000000000 : ℝ)*(f.sum) + (1088195233161/943281250000000000000000000 : ℝ)*base66 + (6771058141557323641/377312500000000000000000000000000 : ℝ)*base67 + (6041524643157823641/377312500000000000000000000000000 : ℝ)*base69 + (2814582155465511141/377312500000000000000000000000000 : ℝ)*base71 + (18916078812339/15092500000000000000000000000 : ℝ)*base73 + (2205297896507386141/377312500000000000000000000000000 : ℝ)*base75 + (3052499691957823641/377312500000000000000000000000000 : ℝ)*base77 + (707229817043051359/377312500000000000000000000000000 : ℝ)*base80 + (1719319715153/30185000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10418689/1250000000000000000000 : ℝ)*base90 + (10418689/1250000000000000000000 : ℝ)*base92 + (10418689/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3190172593799400903135914253/377312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1871874477/100000000000000 : ℝ)*(base19) + (3222893651/100000000000000 : ℝ)*(base23) + (362112699/100000000000000 : ℝ)*(upper3) + (49703021/25000000000000 : ℝ)*(lower4) + (61679343/20000000000000 : ℝ)*(upper5) + (3885038970557393/100000000000000 : ℝ)*(major0) + (3885038970557393/100000000000000 : ℝ)*(major1) + (3885038970557393/100000000000000 : ℝ)*(major2) + (18394956297/50000000000000 : ℝ)*(sp1) + (7196717433/12500000000000 : ℝ)*(sp2) + (2636285386287701/50000000000000 : ℝ)*(sp4) + (527253211078833/10000000000000 : ℝ)*(sp5) + (5272509975942287/100000000000000 : ℝ)*(sp6) + (2497506886706447/100000000000000 : ℝ)*(sp7) + (2497506886706447/100000000000000 : ℝ)*(f.failure) + (2636285386287701/50000000000000 : ℝ)*(f.sum) + (182995503103179/30185000000000000000000000000 : ℝ)*base66 + (1379033257466920249/754625000000000000000000000000000 : ℝ)*base67 + (171327459855579751/754625000000000000000000000000000 : ℝ)*base70 + (6630338913938670249/754625000000000000000000000000000 : ℝ)*base71 + (112064422271039/30185000000000000000000000000 : ℝ)*base74 + (18531422623133170249/754625000000000000000000000000000 : ℝ)*base75 + (2087446004234045249/754625000000000000000000000000000 : ℝ)*base77 + (179607430233829751/754625000000000000000000000000000 : ℝ)*base80 + (156465008720169/30185000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (63138911/10000000000000000000000 : ℝ)*base90 + (63138911/10000000000000000000000 : ℝ)*base92 + (63138911/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1363_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14991/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1363_s4_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025710143/10000000000 : ℝ)*x 0 + (1082766233/2000000000 : ℝ)*x 1 + (2621596141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025710143/10000000000 : ℝ)^4323 ≤ (12340731837763/100000000000000 : ℝ)^3299 := by
    have hnat : (2025710143 : ℕ)^4323*100000000000000^3299 ≤ 12340731837763^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025710143 10000000000 12340731837763 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082766233/2000000000 : ℝ)^4323 ≤ (5593650887843/12500000000000 : ℝ)^3299 := by
    have hnat : (1082766233 : ℕ)^4323*12500000000000^3299 ≤ 5593650887843^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082766233 2000000000 5593650887843 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621596141/5000000000 : ℝ)^4323 ≤ (42910061039097/100000000000000 : ℝ)^3299 := by
    have hnat : (2621596141 : ℕ)^4323*100000000000000^3299 ≤ 42910061039097^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621596141 5000000000 42910061039097 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025710143/10000000000 : ℝ), (1082766233/2000000000 : ℝ), (2621596141/5000000000 : ℝ)] ![(12340731837763/100000000000000 : ℝ), (5593650887843/12500000000000 : ℝ), (42910061039097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025710143/10000000000 : ℝ)|^4323 ≤ (12340731837763/100000000000000 : ℝ)^3299
        have hw : |(-2025710143/10000000000 : ℝ)|=(2025710143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082766233/2000000000 : ℝ)|^4323 ≤ (5593650887843/12500000000000 : ℝ)^3299
        have hw : |(1082766233/2000000000 : ℝ)|=(1082766233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621596141/5000000000 : ℝ)|^4323 ≤ (42910061039097/100000000000000 : ℝ)^3299
        have hw : |(2621596141/5000000000 : ℝ)|=(2621596141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s4_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349192103/10000000000 : ℝ)*x 0 + (-1056337947/5000000000 : ℝ)*x 1 + (327699517/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349192103/10000000000 : ℝ)^4323 ≤ (688287158851/1562500000000 : ℝ)^3299 := by
    have hnat : (5349192103 : ℕ)^4323*1562500000000^3299 ≤ 688287158851^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349192103 10000000000 688287158851 1562500000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056337947/5000000000 : ℝ)^4323 ≤ (13039560890323/100000000000000 : ℝ)^3299 := by
    have hnat : (1056337947 : ℕ)^4323*100000000000000^3299 ≤ 13039560890323^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056337947 5000000000 13039560890323 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327699517/625000000 : ℝ)^4323 ≤ (21455030465927/50000000000000 : ℝ)^3299 := by
    have hnat : (327699517 : ℕ)^4323*50000000000000^3299 ≤ 21455030465927^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327699517 625000000 21455030465927 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349192103/10000000000 : ℝ), (-1056337947/5000000000 : ℝ), (327699517/625000000 : ℝ)] ![(688287158851/1562500000000 : ℝ), (13039560890323/100000000000000 : ℝ), (21455030465927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349192103/10000000000 : ℝ)|^4323 ≤ (688287158851/1562500000000 : ℝ)^3299
        have hw : |(5349192103/10000000000 : ℝ)|=(5349192103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056337947/5000000000 : ℝ)|^4323 ≤ (13039560890323/100000000000000 : ℝ)^3299
        have hw : |(-1056337947/5000000000 : ℝ)|=(1056337947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327699517/625000000 : ℝ)|^4323 ≤ (21455030465927/50000000000000 : ℝ)^3299
        have hw : |(327699517/625000000 : ℝ)|=(327699517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s4_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349192051/10000000000 : ℝ)*x 0 + (1310798083/2500000000 : ℝ)*x 1 + (-2112675883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349192051/10000000000 : ℝ)^4323 ≤ (2753148600333/6250000000000 : ℝ)^3299 := by
    have hnat : (5349192051 : ℕ)^4323*6250000000000^3299 ≤ 2753148600333^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349192051 10000000000 2753148600333 6250000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310798083/2500000000 : ℝ)^4323 ≤ (10727515393827/25000000000000 : ℝ)^3299 := by
    have hnat : (1310798083 : ℕ)^4323*25000000000000^3299 ≤ 10727515393827^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310798083 2500000000 10727515393827 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112675883/10000000000 : ℝ)^4323 ≤ (13039560801357/100000000000000 : ℝ)^3299 := by
    have hnat : (2112675883 : ℕ)^4323*100000000000000^3299 ≤ 13039560801357^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112675883 10000000000 13039560801357 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349192051/10000000000 : ℝ), (1310798083/2500000000 : ℝ), (-2112675883/10000000000 : ℝ)] ![(2753148600333/6250000000000 : ℝ), (10727515393827/25000000000000 : ℝ), (13039560801357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349192051/10000000000 : ℝ)|^4323 ≤ (2753148600333/6250000000000 : ℝ)^3299
        have hw : |(5349192051/10000000000 : ℝ)|=(5349192051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310798083/2500000000 : ℝ)|^4323 ≤ (10727515393827/25000000000000 : ℝ)^3299
        have hw : |(1310798083/2500000000 : ℝ)|=(1310798083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2112675883/10000000000 : ℝ)|^4323 ≤ (13039560801357/100000000000000 : ℝ)^3299
        have hw : |(-2112675883/10000000000 : ℝ)|=(2112675883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s4_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321005753/10000000000 : ℝ)*x 0 + (2072180389/5000000000 : ℝ)*x 1 + (900920441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321005753/10000000000 : ℝ)^4323 ≤ (8325521551863/25000000000000 : ℝ)^3299 := by
    have hnat : (4321005753 : ℕ)^4323*25000000000000^3299 ≤ 8325521551863^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321005753 10000000000 8325521551863 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072180389/5000000000 : ℝ)^4323 ≤ (3941191215773/12500000000000 : ℝ)^3299 := by
    have hnat : (2072180389 : ℕ)^4323*12500000000000^3299 ≤ 3941191215773^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072180389 5000000000 3941191215773 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900920441/2000000000 : ℝ)^4323 ≤ (35168384056597/100000000000000 : ℝ)^3299 := by
    have hnat : (900920441 : ℕ)^4323*100000000000000^3299 ≤ 35168384056597^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900920441 2000000000 35168384056597 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321005753/10000000000 : ℝ), (2072180389/5000000000 : ℝ), (900920441/2000000000 : ℝ)] ![(8325521551863/25000000000000 : ℝ), (3941191215773/12500000000000 : ℝ), (35168384056597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321005753/10000000000 : ℝ)|^4323 ≤ (8325521551863/25000000000000 : ℝ)^3299
        have hw : |(4321005753/10000000000 : ℝ)|=(4321005753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072180389/5000000000 : ℝ)|^4323 ≤ (3941191215773/12500000000000 : ℝ)^3299
        have hw : |(2072180389/5000000000 : ℝ)|=(2072180389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900920441/2000000000 : ℝ)|^4323 ≤ (35168384056597/100000000000000 : ℝ)^3299
        have hw : |(900920441/2000000000 : ℝ)|=(900920441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s4_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1012861503/5000000000 : ℝ)*x 0 + (20975279/40000000 : ℝ)*x 1 + (5413200401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012861503/5000000000 : ℝ)^4323 ≤ (1542604315411/12500000000000 : ℝ)^3299 := by
    have hnat : (1012861503 : ℕ)^4323*12500000000000^3299 ≤ 1542604315411^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012861503 5000000000 1542604315411 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20975279/40000000 : ℝ)^4323 ≤ (8583358055503/20000000000000 : ℝ)^3299 := by
    have hnat : (20975279 : ℕ)^4323*20000000000000^3299 ≤ 8583358055503^3299*40000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20975279 40000000 8583358055503 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413200401/10000000000 : ℝ)^4323 ≤ (2237118759271/5000000000000 : ℝ)^3299 := by
    have hnat : (5413200401 : ℕ)^4323*5000000000000^3299 ≤ 2237118759271^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413200401 10000000000 2237118759271 5000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1012861503/5000000000 : ℝ), (20975279/40000000 : ℝ), (5413200401/10000000000 : ℝ)] ![(1542604315411/12500000000000 : ℝ), (8583358055503/20000000000000 : ℝ), (2237118759271/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1012861503/5000000000 : ℝ)|^4323 ≤ (1542604315411/12500000000000 : ℝ)^3299
        have hw : |(-1012861503/5000000000 : ℝ)|=(1012861503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20975279/40000000 : ℝ)|^4323 ≤ (8583358055503/20000000000000 : ℝ)^3299
        have hw : |(20975279/40000000 : ℝ)|=(20975279/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413200401/10000000000 : ℝ)|^4323 ≤ (2237118759271/5000000000000 : ℝ)^3299
        have hw : |(5413200401/10000000000 : ℝ)|=(5413200401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s4_5 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530513503/1000000000 : ℝ)*x 0 + (-9713339/50000000 : ℝ)*x 1 + (2706600119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530513503/1000000000 : ℝ)^4323 ≤ (10893891056873/25000000000000 : ℝ)^3299 := by
    have hnat : (530513503 : ℕ)^4323*25000000000000^3299 ≤ 10893891056873^3299*1000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530513503 1000000000 10893891056873 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9713339/50000000 : ℝ)^4323 ≤ (11682062349841/100000000000000 : ℝ)^3299 := by
    have hnat : (9713339 : ℕ)^4323*100000000000000^3299 ≤ 11682062349841^3299*50000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9713339 50000000 11682062349841 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706600119/5000000000 : ℝ)^4323 ≤ (4474237341997/10000000000000 : ℝ)^3299 := by
    have hnat : (2706600119 : ℕ)^4323*10000000000000^3299 ≤ 4474237341997^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706600119 5000000000 4474237341997 10000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530513503/1000000000 : ℝ), (-9713339/50000000 : ℝ), (2706600119/5000000000 : ℝ)] ![(10893891056873/25000000000000 : ℝ), (11682062349841/100000000000000 : ℝ), (4474237341997/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530513503/1000000000 : ℝ)|^4323 ≤ (10893891056873/25000000000000 : ℝ)^3299
        have hw : |(530513503/1000000000 : ℝ)|=(530513503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9713339/50000000 : ℝ)|^4323 ≤ (11682062349841/100000000000000 : ℝ)^3299
        have hw : |(-9713339/50000000 : ℝ)|=(9713339/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706600119/5000000000 : ℝ)|^4323 ≤ (4474237341997/10000000000000 : ℝ)^3299
        have hw : |(2706600119/5000000000 : ℝ)|=(2706600119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s4_6 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305134917/10000000000 : ℝ)*x 0 + (5413200341/10000000000 : ℝ)*x 1 + (-485666953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305134917/10000000000 : ℝ)^4323 ≤ (10893890752807/25000000000000 : ℝ)^3299 := by
    have hnat : (5305134917 : ℕ)^4323*25000000000000^3299 ≤ 10893890752807^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305134917 10000000000 10893890752807 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413200341/10000000000 : ℝ)^4323 ≤ (44742374535561/100000000000000 : ℝ)^3299 := by
    have hnat : (5413200341 : ℕ)^4323*100000000000000^3299 ≤ 44742374535561^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413200341 10000000000 44742374535561 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485666953/2500000000 : ℝ)^4323 ≤ (29205156111/250000000000 : ℝ)^3299 := by
    have hnat : (485666953 : ℕ)^4323*250000000000^3299 ≤ 29205156111^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485666953 2500000000 29205156111 250000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305134917/10000000000 : ℝ), (5413200341/10000000000 : ℝ), (-485666953/2500000000 : ℝ)] ![(10893890752807/25000000000000 : ℝ), (44742374535561/100000000000000 : ℝ), (29205156111/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305134917/10000000000 : ℝ)|^4323 ≤ (10893890752807/25000000000000 : ℝ)^3299
        have hw : |(5305134917/10000000000 : ℝ)|=(5305134917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413200341/10000000000 : ℝ)|^4323 ≤ (44742374535561/100000000000000 : ℝ)^3299
        have hw : |(5413200341/10000000000 : ℝ)|=(5413200341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485666953/2500000000 : ℝ)|^4323 ≤ (29205156111/250000000000 : ℝ)^3299
        have hw : |(-485666953/2500000000 : ℝ)|=(485666953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s4_7 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080258149/2500000000 : ℝ)*x 0 + (2251638819/5000000000 : ℝ)*x 1 + (2072846369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080258149/2500000000 : ℝ)^4323 ≤ (16651178651063/50000000000000 : ℝ)^3299 := by
    have hnat : (1080258149 : ℕ)^4323*50000000000000^3299 ≤ 16651178651063^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080258149 2500000000 16651178651063 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251638819/5000000000 : ℝ)^4323 ≤ (17577416814529/50000000000000 : ℝ)^3299 := by
    have hnat : (2251638819 : ℕ)^4323*50000000000000^3299 ≤ 17577416814529^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251638819 5000000000 17577416814529 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072846369/5000000000 : ℝ)^4323 ≤ (31542809042047/100000000000000 : ℝ)^3299 := by
    have hnat : (2072846369 : ℕ)^4323*100000000000000^3299 ≤ 31542809042047^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072846369 5000000000 31542809042047 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080258149/2500000000 : ℝ), (2251638819/5000000000 : ℝ), (2072846369/5000000000 : ℝ)] ![(16651178651063/50000000000000 : ℝ), (17577416814529/50000000000000 : ℝ), (31542809042047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080258149/2500000000 : ℝ)|^4323 ≤ (16651178651063/50000000000000 : ℝ)^3299
        have hw : |(1080258149/2500000000 : ℝ)|=(1080258149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251638819/5000000000 : ℝ)|^4323 ≤ (17577416814529/50000000000000 : ℝ)^3299
        have hw : |(2251638819/5000000000 : ℝ)|=(2251638819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072846369/5000000000 : ℝ)|^4323 ≤ (31542809042047/100000000000000 : ℝ)^3299
        have hw : |(2072846369/5000000000 : ℝ)|=(2072846369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5577/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10943/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (8799945804360701/100000000000000000000 : ℝ) := by
    have hpowers : (10943/100000 : ℝ)^2161 ≤ (8799945804360701/100000000000000000000 : ℝ)^512 := by
      have hnat : (10943 : ℕ)^2161*100000000000000000000^512 ≤ 8799945804360701^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10943 100000 8799945804360701 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10943/100000 : ℝ)) (X := (8799945804360701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14991/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (33221990939961889/100000000000000000000 : ℝ) := by
    have hpowers : (14991/100000 : ℝ)^2161 ≤ (33221990939961889/100000000000000000000 : ℝ)^512 := by
      have hnat : (14991 : ℕ)^2161*100000000000000000000^512 ≤ 33221990939961889^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14991 100000 33221990939961889 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14991/100000 : ℝ)) (X := (33221990939961889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008799945804360701/50000000000000000000 : ℝ) ≤ (10000416961567241/10000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50008799945804360701/50000000000000000000 : ℝ)^512 ≤ (10000416961567241/10000000000000000 : ℝ)^2161 := by
      have hnat : (50008799945804360701 : ℕ)^512*10000000000000000^2161 ≤ 10000416961567241^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008799945804360701 50000000000000000000 10000416961567241 10000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000416961567241/10000000000000000 : ℝ)) (X := (50008799945804360701/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004202193674432259/10000000000000000000 : ℝ) ≤ (5000497727509259/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (10004202193674432259/10000000000000000000 : ℝ)^512 ≤ (5000497727509259/5000000000000000 : ℝ)^2161 := by
      have hnat : (10004202193674432259 : ℕ)^512*5000000000000000^2161 ≤ 5000497727509259^2161*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004202193674432259 10000000000000000000 5000497727509259 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000497727509259/5000000000000000 : ℝ)) (X := (10004202193674432259/10000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033221990939961889/50000000000000000000 : ℝ) ≤ (2000314789693959/2000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50033221990939961889/50000000000000000000 : ℝ)^512 ≤ (2000314789693959/2000000000000000 : ℝ)^2161 := by
      have hnat : (50033221990939961889 : ℕ)^512*2000000000000000^2161 ≤ 2000314789693959^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033221990939961889 50000000000000000000 2000314789693959 2000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000314789693959/2000000000000000 : ℝ)) (X := (50033221990939961889/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8799945804360701/100000000000000000000 : ℝ) ≤ ((20234513476374771573/20240000000000000000 : ℝ)+2*(578493451277/404800000000000 : ℝ)*(10943/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (20234513476374771573/20240000000000000000 : ℝ)+2*(578493451277/404800000000000 : ℝ)*(10943/100000 : ℝ)=(10000416961567241/10000000000000000 : ℝ) by norm_num, show 1+2*(8799945804360701/100000000000000000000 : ℝ)=(50008799945804360701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33221990939961889/100000000000000000000 : ℝ)+(8799945804360701/100000000000000000000 : ℝ) ≤ ((20234513476374771573/20240000000000000000 : ℝ)+(578493451277/404800000000000 : ℝ)*((14991/100000 : ℝ)+(10943/100000 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (20234513476374771573/20240000000000000000 : ℝ)+(578493451277/404800000000000 : ℝ)*((14991/100000 : ℝ)+(10943/100000 : ℝ))=(5000497727509259/5000000000000000 : ℝ) by norm_num, show 1+(33221990939961889/100000000000000000000 : ℝ)+(8799945804360701/100000000000000000000 : ℝ)=(10004202193674432259/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33221990939961889/100000000000000000000 : ℝ) ≤ ((20234513476374771573/20240000000000000000 : ℝ)+2*(578493451277/404800000000000 : ℝ)*(14991/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (20234513476374771573/20240000000000000000 : ℝ)+2*(578493451277/404800000000000 : ℝ)*(14991/100000 : ℝ)=(2000314789693959/2000000000000000 : ℝ) by norm_num, show 1+2*(33221990939961889/100000000000000000000 : ℝ)=(50033221990939961889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20234513476374771573/20240000000000000000 : ℝ)*(X 1 0+X 2 0)+(578493451277/404800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (14991/100000 : ℝ)) (c := (20234513476374771573/20240000000000000000 : ℝ)) (alpha := (578493451277/404800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20234513476374771573/20240000000000000000 : ℝ)*(X 0 1+X 2 1)+(578493451277/404800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (14991/100000 : ℝ)) (c := (20234513476374771573/20240000000000000000 : ℝ)) (alpha := (578493451277/404800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20234513476374771573/20240000000000000000 : ℝ)*(X 0 2+X 1 2)+(578493451277/404800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (14991/100000 : ℝ)) (c := (20234513476374771573/20240000000000000000 : ℝ)) (alpha := (578493451277/404800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2025710143/10000000000 : ℝ)*X 0 0+(1082766233/2000000000 : ℝ)*X 0 1+(2621596141/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349192103/10000000000 : ℝ)*X 1 0+(-1056337947/5000000000 : ℝ)*X 1 1+(327699517/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349192051/10000000000 : ℝ)*X 2 0+(1310798083/2500000000 : ℝ)*X 2 1+(-2112675883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321005753/10000000000 : ℝ)*X 0 0+(2072180389/5000000000 : ℝ)*X 0 1+(900920441/2000000000 : ℝ)*X 0 2+(4321005753/10000000000 : ℝ)*X 1 0+(2072180389/5000000000 : ℝ)*X 1 1+(900920441/2000000000 : ℝ)*X 1 2+(4321005753/10000000000 : ℝ)*X 2 0+(2072180389/5000000000 : ℝ)*X 2 1+(900920441/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1012861503/5000000000 : ℝ)*X 0 0+(20975279/40000000 : ℝ)*X 0 1+(5413200401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530513503/1000000000 : ℝ)*X 1 0+(-9713339/50000000 : ℝ)*X 1 1+(2706600119/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305134917/10000000000 : ℝ)*X 2 0+(5413200341/10000000000 : ℝ)*X 2 1+(-485666953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080258149/2500000000 : ℝ)*X 0 0+(2251638819/5000000000 : ℝ)*X 0 1+(2072846369/5000000000 : ℝ)*X 0 2+(1080258149/2500000000 : ℝ)*X 1 0+(2251638819/5000000000 : ℝ)*X 1 1+(2072846369/5000000000 : ℝ)*X 1 2+(1080258149/2500000000 : ℝ)*X 2 0+(2251638819/5000000000 : ℝ)*X 2 1+(2072846369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9490736444683492209651/1840000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102741957/10000000000000 : ℝ)*(base19) + (911000863/100000000000000 : ℝ)*(base23) + (15900333/50000000000000 : ℝ)*(lower2) + (57462291/50000000000000 : ℝ)*(upper3) + (73887693/100000000000000 : ℝ)*(upper5) + (4318155106048883/100000000000000 : ℝ)*(major0) + (4318155106048883/100000000000000 : ℝ)*(major1) + (4318155106048883/100000000000000 : ℝ)*(major2) + (5860351734825237/100000000000000 : ℝ)*(sp0) + (5860372349829589/100000000000000 : ℝ)*(sp1) + (1172074493249659/20000000000000 : ℝ)*(sp2) + (1387963028233147/50000000000000 : ℝ)*(sp3) + (21642423921/100000000000000 : ℝ)*(sp4) + (5303224337/50000000000000 : ℝ)*(sp7) + (2775936662914969/100000000000000 : ℝ)*(f.failure) + (2930186688624579/50000000000000 : ℝ)*(f.sum) + (14397169144821/1840000000000000000000000000 : ℝ)*base65 + (682570418181850269/184000000000000000000000000000000 : ℝ)*base67 + (1475297390389850269/184000000000000000000000000000000 : ℝ)*base69 + (653928882154149731/184000000000000000000000000000000 : ℝ)*base72 + (13327246848261/1840000000000000000000000000 : ℝ)*base73 + (2303202051362149731/184000000000000000000000000000000 : ℝ)*base76 + (352225920293850269/184000000000000000000000000000000 : ℝ)*base77 + (1238522629458149731/184000000000000000000000000000000 : ℝ)*base80 + (3699636333301/1840000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (40347703/10000000000000000000000 : ℝ)*base89 + (40347703/10000000000000000000000 : ℝ)*base91 + (40347703/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1131444504361979583153/460000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220277127/50000000000000 : ℝ)*(base19) + (228285701/50000000000000 : ℝ)*(base23) + (73836457/100000000000000 : ℝ)*(upper2) + (47730309/100000000000000 : ℝ)*(lower3) + (1087550105735071/25000000000000 : ℝ)*(major0) + (1087550105735071/25000000000000 : ℝ)*(major1) + (1087550105735071/25000000000000 : ℝ)*(major2) + (1254176763/100000000000000 : ℝ)*(sp0) + (1285915987/12500000000000 : ℝ)*(sp1) + (10599297727/100000000000000 : ℝ)*(sp2) + (59038624357799/1000000000000 : ℝ)*(sp4) + (5903852962074513/100000000000000 : ℝ)*(sp5) + (2951926317043767/50000000000000 : ℝ)*(sp6) + (1398268536967583/50000000000000 : ℝ)*(sp7) + (1398268536967583/50000000000000 : ℝ)*(f.failure) + (5903863689956663/100000000000000 : ℝ)*(f.sum) + (4050893687723/460000000000000000000000000 : ℝ)*base66 + (295533290514064847/46000000000000000000000000000000 : ℝ)*base68 + (171769404019935153/46000000000000000000000000000000 : ℝ)*base69 + (44240111820064847/46000000000000000000000000000000 : ℝ)*base72 + (1833975693943/460000000000000000000000000 : ℝ)*base74 + (303813749979935153/46000000000000000000000000000000 : ℝ)*base75 + (774135777362064847/46000000000000000000000000000000 : ℝ)*base78 + (539696319587935153/46000000000000000000000000000000 : ℝ)*base79 + (617852292443/460000000000000000000000000 : ℝ)*base82 + (37877521/5000000000000000000000 : ℝ)*base89 + (37877521/5000000000000000000000 : ℝ)*base91 + (37877521/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1363_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1363_s5_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1012964519/5000000000 : ℝ)*x 0 + (270597209/500000000 : ℝ)*x 1 + (262246749/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012964519/5000000000 : ℝ)^4323 ≤ (493699172299/4000000000000 : ℝ)^3299 := by
    have hnat : (1012964519 : ℕ)^4323*4000000000000^3299 ≤ 493699172299^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012964519 5000000000 493699172299 4000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270597209/500000000 : ℝ)^4323 ≤ (44728769567953/100000000000000 : ℝ)^3299 := by
    have hnat : (270597209 : ℕ)^4323*100000000000000^3299 ≤ 44728769567953^3299*500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270597209 500000000 44728769567953 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262246749/500000000 : ℝ)^4323 ≤ (21464375551809/50000000000000 : ℝ)^3299 := by
    have hnat : (262246749 : ℕ)^4323*50000000000000^3299 ≤ 21464375551809^3299*500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262246749 500000000 21464375551809 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1012964519/5000000000 : ℝ), (270597209/500000000 : ℝ), (262246749/500000000 : ℝ)] ![(493699172299/4000000000000 : ℝ), (44728769567953/100000000000000 : ℝ), (21464375551809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1012964519/5000000000 : ℝ)|^4323 ≤ (493699172299/4000000000000 : ℝ)^3299
        have hw : |(-1012964519/5000000000 : ℝ)|=(1012964519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270597209/500000000 : ℝ)|^4323 ≤ (44728769567953/100000000000000 : ℝ)^3299
        have hw : |(270597209/500000000 : ℝ)|=(270597209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262246749/500000000 : ℝ)|^4323 ≤ (21464375551809/50000000000000 : ℝ)^3299
        have hw : |(262246749/500000000 : ℝ)|=(262246749/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s5_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674354027/5000000000 : ℝ)*x 0 + (-2111010543/10000000000 : ℝ)*x 1 + (5244935037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674354027/5000000000 : ℝ)^4323 ≤ (8809030966981/20000000000000 : ℝ)^3299 := by
    have hnat : (2674354027 : ℕ)^4323*20000000000000^3299 ≤ 8809030966981^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674354027 5000000000 8809030966981 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111010543/10000000000 : ℝ)^4323 ≤ (13026093431747/100000000000000 : ℝ)^3299 := by
    have hnat : (2111010543 : ℕ)^4323*100000000000000^3299 ≤ 13026093431747^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111010543 10000000000 13026093431747 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244935037/10000000000 : ℝ)^4323 ≤ (21464375857481/50000000000000 : ℝ)^3299 := by
    have hnat : (5244935037 : ℕ)^4323*50000000000000^3299 ≤ 21464375857481^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244935037 10000000000 21464375857481 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674354027/5000000000 : ℝ), (-2111010543/10000000000 : ℝ), (5244935037/10000000000 : ℝ)] ![(8809030966981/20000000000000 : ℝ), (13026093431747/100000000000000 : ℝ), (21464375857481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674354027/5000000000 : ℝ)|^4323 ≤ (8809030966981/20000000000000 : ℝ)^3299
        have hw : |(2674354027/5000000000 : ℝ)|=(2674354027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2111010543/10000000000 : ℝ)|^4323 ≤ (13026093431747/100000000000000 : ℝ)^3299
        have hw : |(-2111010543/10000000000 : ℝ)|=(2111010543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244935037/10000000000 : ℝ)|^4323 ≤ (21464375857481/50000000000000 : ℝ)^3299
        have hw : |(5244935037/10000000000 : ℝ)|=(5244935037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s5_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674353989/5000000000 : ℝ)*x 0 + (655616897/1250000000 : ℝ)*x 1 + (-2111010461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674353989/5000000000 : ℝ)^4323 ≤ (44045154014807/100000000000000 : ℝ)^3299 := by
    have hnat : (2674353989 : ℕ)^4323*100000000000000^3299 ≤ 44045154014807^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674353989 5000000000 44045154014807 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655616897/1250000000 : ℝ)^4323 ≤ (5366094150723/12500000000000 : ℝ)^3299 := by
    have hnat : (655616897 : ℕ)^4323*12500000000000^3299 ≤ 5366094150723^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655616897 1250000000 5366094150723 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111010461/10000000000 : ℝ)^4323 ≤ (6513046384353/50000000000000 : ℝ)^3299 := by
    have hnat : (2111010461 : ℕ)^4323*50000000000000^3299 ≤ 6513046384353^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111010461 10000000000 6513046384353 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674353989/5000000000 : ℝ), (655616897/1250000000 : ℝ), (-2111010461/10000000000 : ℝ)] ![(44045154014807/100000000000000 : ℝ), (5366094150723/12500000000000 : ℝ), (6513046384353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674353989/5000000000 : ℝ)|^4323 ≤ (44045154014807/100000000000000 : ℝ)^3299
        have hw : |(2674353989/5000000000 : ℝ)|=(2674353989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655616897/1250000000 : ℝ)|^4323 ≤ (5366094150723/12500000000000 : ℝ)^3299
        have hw : |(655616897/1250000000 : ℝ)|=(655616897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111010461/10000000000 : ℝ)|^4323 ≤ (6513046384353/50000000000000 : ℝ)^3299
        have hw : |(-2111010461/10000000000 : ℝ)|=(2111010461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s5_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321135933/10000000000 : ℝ)*x 0 + (1037044071/2500000000 : ℝ)*x 1 + (900150919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321135933/10000000000 : ℝ)^4323 ≤ (16651700467577/50000000000000 : ℝ)^3299 := by
    have hnat : (4321135933 : ℕ)^4323*50000000000000^3299 ≤ 16651700467577^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321135933 10000000000 16651700467577 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037044071/2500000000 : ℝ)^4323 ≤ (31567572925711/100000000000000 : ℝ)^3299 := by
    have hnat : (1037044071 : ℕ)^4323*100000000000000^3299 ≤ 31567572925711^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037044071 2500000000 31567572925711 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900150919/2000000000 : ℝ)^4323 ≤ (35129026117741/100000000000000 : ℝ)^3299 := by
    have hnat : (900150919 : ℕ)^4323*100000000000000^3299 ≤ 35129026117741^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900150919 2000000000 35129026117741 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321135933/10000000000 : ℝ), (1037044071/2500000000 : ℝ), (900150919/2000000000 : ℝ)] ![(16651700467577/50000000000000 : ℝ), (31567572925711/100000000000000 : ℝ), (35129026117741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321135933/10000000000 : ℝ)|^4323 ≤ (16651700467577/50000000000000 : ℝ)^3299
        have hw : |(4321135933/10000000000 : ℝ)|=(4321135933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037044071/2500000000 : ℝ)|^4323 ≤ (31567572925711/100000000000000 : ℝ)^3299
        have hw : |(1037044071/2500000000 : ℝ)|=(1037044071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900150919/2000000000 : ℝ)|^4323 ≤ (35129026117741/100000000000000 : ℝ)^3299
        have hw : |(900150919/2000000000 : ℝ)|=(900150919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s5_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025940919/10000000000 : ℝ)*x 0 + (262276821/500000000 : ℝ)*x 1 + (1082267957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025940919/10000000000 : ℝ)^4323 ≤ (6171287078427/50000000000000 : ℝ)^3299 := by
    have hnat : (2025940919 : ℕ)^4323*50000000000000^3299 ≤ 6171287078427^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025940919 10000000000 6171287078427 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262276821/500000000 : ℝ)^4323 ≤ (42935201866857/100000000000000 : ℝ)^3299 := by
    have hnat : (262276821 : ℕ)^4323*100000000000000^3299 ≤ 42935201866857^3299*500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262276821 500000000 42935201866857 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082267957/2000000000 : ℝ)^4323 ≤ (44722223961381/100000000000000 : ℝ)^3299 := by
    have hnat : (1082267957 : ℕ)^4323*100000000000000^3299 ≤ 44722223961381^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082267957 2000000000 44722223961381 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025940919/10000000000 : ℝ), (262276821/500000000 : ℝ), (1082267957/2000000000 : ℝ)] ![(6171287078427/50000000000000 : ℝ), (42935201866857/100000000000000 : ℝ), (44722223961381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025940919/10000000000 : ℝ)|^4323 ≤ (6171287078427/50000000000000 : ℝ)^3299
        have hw : |(-2025940919/10000000000 : ℝ)|=(2025940919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262276821/500000000 : ℝ)|^4323 ≤ (42935201866857/100000000000000 : ℝ)^3299
        have hw : |(262276821/500000000 : ℝ)|=(262276821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082267957/2000000000 : ℝ)|^4323 ≤ (44722223961381/100000000000000 : ℝ)^3299
        have hw : |(1082267957/2000000000 : ℝ)|=(1082267957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s5_5 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663198467/1250000000 : ℝ)*x 0 + (-243075737/1250000000 : ℝ)*x 1 + (5411339993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663198467/1250000000 : ℝ)^4323 ≤ (43580436947969/100000000000000 : ℝ)^3299 := by
    have hnat : (663198467 : ℕ)^4323*100000000000000^3299 ≤ 43580436947969^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663198467 1250000000 43580436947969 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243075737/1250000000 : ℝ)^4323 ≤ (731083551803/6250000000000 : ℝ)^3299 := by
    have hnat : (243075737 : ℕ)^4323*6250000000000^3299 ≤ 731083551803^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243075737 1250000000 731083551803 6250000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411339993/10000000000 : ℝ)^4323 ≤ (8944445242797/20000000000000 : ℝ)^3299 := by
    have hnat : (5411339993 : ℕ)^4323*20000000000000^3299 ≤ 8944445242797^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411339993 10000000000 8944445242797 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663198467/1250000000 : ℝ), (-243075737/1250000000 : ℝ), (5411339993/10000000000 : ℝ)] ![(43580436947969/100000000000000 : ℝ), (731083551803/6250000000000 : ℝ), (8944445242797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663198467/1250000000 : ℝ)|^4323 ≤ (43580436947969/100000000000000 : ℝ)^3299
        have hw : |(663198467/1250000000 : ℝ)|=(663198467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243075737/1250000000 : ℝ)|^4323 ≤ (731083551803/6250000000000 : ℝ)^3299
        have hw : |(-243075737/1250000000 : ℝ)|=(243075737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411339993/10000000000 : ℝ)|^4323 ≤ (8944445242797/20000000000000 : ℝ)^3299
        have hw : |(5411339993/10000000000 : ℝ)|=(5411339993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s5_6 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305587577/10000000000 : ℝ)*x 0 + (5411340191/10000000000 : ℝ)*x 1 + (-1944605839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305587577/10000000000 : ℝ)^4323 ≤ (43580435236543/100000000000000 : ℝ)^3299 := by
    have hnat : (5305587577 : ℕ)^4323*100000000000000^3299 ≤ 43580435236543^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305587577 10000000000 43580435236543 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411340191/10000000000 : ℝ)^4323 ≤ (4472222835829/10000000000000 : ℝ)^3299 := by
    have hnat : (5411340191 : ℕ)^4323*10000000000000^3299 ≤ 4472222835829^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411340191 10000000000 4472222835829 10000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944605839/10000000000 : ℝ)^4323 ≤ (11697336379551/100000000000000 : ℝ)^3299 := by
    have hnat : (1944605839 : ℕ)^4323*100000000000000^3299 ≤ 11697336379551^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944605839 10000000000 11697336379551 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305587577/10000000000 : ℝ), (5411340191/10000000000 : ℝ), (-1944605839/10000000000 : ℝ)] ![(43580435236543/100000000000000 : ℝ), (4472222835829/10000000000000 : ℝ), (11697336379551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305587577/10000000000 : ℝ)|^4323 ≤ (43580435236543/100000000000000 : ℝ)^3299
        have hw : |(5305587577/10000000000 : ℝ)|=(5305587577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411340191/10000000000 : ℝ)|^4323 ≤ (4472222835829/10000000000000 : ℝ)^3299
        have hw : |(5411340191/10000000000 : ℝ)|=(5411340191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1944605839/10000000000 : ℝ)|^4323 ≤ (11697336379551/100000000000000 : ℝ)^3299
        have hw : |(-1944605839/10000000000 : ℝ)|=(1944605839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s5_7 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321161333/10000000000 : ℝ)*x 0 + (2249742827/5000000000 : ℝ)*x 1 + (165978077/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321161333/10000000000 : ℝ)^4323 ≤ (33303657458969/100000000000000 : ℝ)^3299 := by
    have hnat : (4321161333 : ℕ)^4323*100000000000000^3299 ≤ 33303657458969^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321161333 10000000000 33303657458969 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249742827/5000000000 : ℝ)^4323 ≤ (35116048167001/100000000000000 : ℝ)^3299 := by
    have hnat : (2249742827 : ℕ)^4323*100000000000000^3299 ≤ 35116048167001^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249742827 5000000000 35116048167001 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165978077/400000000 : ℝ)^4323 ≤ (315802943607/1000000000000 : ℝ)^3299 := by
    have hnat : (165978077 : ℕ)^4323*1000000000000^3299 ≤ 315802943607^3299*400000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165978077 400000000 315802943607 1000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321161333/10000000000 : ℝ), (2249742827/5000000000 : ℝ), (165978077/400000000 : ℝ)] ![(33303657458969/100000000000000 : ℝ), (35116048167001/100000000000000 : ℝ), (315802943607/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321161333/10000000000 : ℝ)|^4323 ≤ (33303657458969/100000000000000 : ℝ)^3299
        have hw : |(4321161333/10000000000 : ℝ)|=(4321161333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249742827/5000000000 : ℝ)|^4323 ≤ (35116048167001/100000000000000 : ℝ)^3299
        have hw : |(2249742827/5000000000 : ℝ)|=(2249742827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165978077/400000000 : ℝ)|^4323 ≤ (315802943607/1000000000000 : ℝ)^3299
        have hw : |(165978077/400000000 : ℝ)|=(165978077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11191/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14727/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5577/50000 : ℝ) ^ (2161/512 : ℝ) ≤ (953866345348153/10000000000000000000 : ℝ) := by
    have hpowers : (5577/50000 : ℝ)^2161 ≤ (953866345348153/10000000000000000000 : ℝ)^512 := by
      have hnat : (5577 : ℕ)^2161*10000000000000000000^512 ≤ 953866345348153^512*50000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5577 50000 953866345348153 10000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5577/50000 : ℝ)) (X := (953866345348153/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (2161/512 : ℝ) ≤ (31167730099766831/100000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^2161 ≤ (31167730099766831/100000000000000000000 : ℝ)^512 := by
      have hnat : (7383 : ℕ)^2161*100000000000000000000^512 ≤ 31167730099766831^512*50000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 31167730099766831 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (31167730099766831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000953866345348153/5000000000000000000 : ℝ) ≤ (5000225980576193/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (5000953866345348153/5000000000000000000 : ℝ)^512 ≤ (5000225980576193/5000000000000000 : ℝ)^2161 := by
      have hnat : (5000953866345348153 : ℕ)^512*5000000000000000^2161 ≤ 5000225980576193^2161*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000953866345348153 5000000000000000000 5000225980576193 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000225980576193/5000000000000000 : ℝ)) (X := (5000953866345348153/5000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040706393553248361/100000000000000000000 : ℝ) ≤ (10000964296037011/10000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (100040706393553248361/100000000000000000000 : ℝ)^512 ≤ (10000964296037011/10000000000000000 : ℝ)^2161 := by
      have hnat : (100040706393553248361 : ℕ)^512*10000000000000000^2161 ≤ 10000964296037011^2161*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040706393553248361 100000000000000000000 10000964296037011 10000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000964296037011/10000000000000000 : ℝ)) (X := (100040706393553248361/100000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031167730099766831/50000000000000000000 : ℝ) ≤ (2500369157730409/2500000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50031167730099766831/50000000000000000000 : ℝ)^512 ≤ (2500369157730409/2500000000000000 : ℝ)^2161 := by
      have hnat : (50031167730099766831 : ℕ)^512*2500000000000000^2161 ≤ 2500369157730409^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031167730099766831 50000000000000000000 2500369157730409 2500000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500369157730409/2500000000000000 : ℝ)) (X := (50031167730099766831/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(953866345348153/10000000000000000000 : ℝ) ≤ ((3009183609756350311/3010000000000000000 : ℝ)+2*(1366226359/963200000000 : ℝ)*(5577/50000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (3009183609756350311/3010000000000000000 : ℝ)+2*(1366226359/963200000000 : ℝ)*(5577/50000 : ℝ)=(5000225980576193/5000000000000000 : ℝ) by norm_num, show 1+2*(953866345348153/10000000000000000000 : ℝ)=(5000953866345348153/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31167730099766831/100000000000000000000 : ℝ)+(953866345348153/10000000000000000000 : ℝ) ≤ ((3009183609756350311/3010000000000000000 : ℝ)+(1366226359/963200000000 : ℝ)*((7383/50000 : ℝ)+(5577/50000 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (3009183609756350311/3010000000000000000 : ℝ)+(1366226359/963200000000 : ℝ)*((7383/50000 : ℝ)+(5577/50000 : ℝ))=(10000964296037011/10000000000000000 : ℝ) by norm_num, show 1+(31167730099766831/100000000000000000000 : ℝ)+(953866345348153/10000000000000000000 : ℝ)=(100040706393553248361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31167730099766831/100000000000000000000 : ℝ) ≤ ((3009183609756350311/3010000000000000000 : ℝ)+2*(1366226359/963200000000 : ℝ)*(7383/50000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (3009183609756350311/3010000000000000000 : ℝ)+2*(1366226359/963200000000 : ℝ)*(7383/50000 : ℝ)=(2500369157730409/2500000000000000 : ℝ) by norm_num, show 1+2*(31167730099766831/100000000000000000000 : ℝ)=(50031167730099766831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3009183609756350311/3010000000000000000 : ℝ)*(X 1 0+X 2 0)+(1366226359/963200000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (3009183609756350311/3010000000000000000 : ℝ)) (alpha := (1366226359/963200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3009183609756350311/3010000000000000000 : ℝ)*(X 0 1+X 2 1)+(1366226359/963200000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (3009183609756350311/3010000000000000000 : ℝ)) (alpha := (1366226359/963200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3009183609756350311/3010000000000000000 : ℝ)*(X 0 2+X 1 2)+(1366226359/963200000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (3009183609756350311/3010000000000000000 : ℝ)) (alpha := (1366226359/963200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1012964519/5000000000 : ℝ)*X 0 0+(270597209/500000000 : ℝ)*X 0 1+(262246749/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674354027/5000000000 : ℝ)*X 1 0+(-2111010543/10000000000 : ℝ)*X 1 1+(5244935037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674353989/5000000000 : ℝ)*X 2 0+(655616897/1250000000 : ℝ)*X 2 1+(-2111010461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321135933/10000000000 : ℝ)*X 0 0+(1037044071/2500000000 : ℝ)*X 0 1+(900150919/2000000000 : ℝ)*X 0 2+(4321135933/10000000000 : ℝ)*X 1 0+(1037044071/2500000000 : ℝ)*X 1 1+(900150919/2000000000 : ℝ)*X 1 2+(4321135933/10000000000 : ℝ)*X 2 0+(1037044071/2500000000 : ℝ)*X 2 1+(900150919/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2025940919/10000000000 : ℝ)*X 0 0+(262276821/500000000 : ℝ)*X 0 1+(1082267957/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663198467/1250000000 : ℝ)*X 1 0+(-243075737/1250000000 : ℝ)*X 1 1+(5411339993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305587577/10000000000 : ℝ)*X 2 0+(5411340191/10000000000 : ℝ)*X 2 1+(-1944605839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321161333/10000000000 : ℝ)*X 0 0+(2249742827/5000000000 : ℝ)*X 0 1+(165978077/400000000 : ℝ)*X 0 2+(4321161333/10000000000 : ℝ)*X 1 0+(2249742827/5000000000 : ℝ)*X 1 1+(165978077/400000000 : ℝ)*X 1 2+(4321161333/10000000000 : ℝ)*X 2 0+(2249742827/5000000000 : ℝ)*X 2 1+(165978077/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1950798352164060705549/301000000000000000000000000 : ℝ) := by norm_num
    linear_combination (391743853/25000000000000 : ℝ)*(base19) + (140817939/10000000000000 : ℝ)*(base23) + (32235067/20000000000000 : ℝ)*(upper3) + (39428341/100000000000000 : ℝ)*(upper4) + (195341337/100000000000000 : ℝ)*(upper5) + (110300586233199/2500000000000 : ℝ)*(major0) + (110300586233199/2500000000000 : ℝ)*(major1) + (110300586233199/2500000000000 : ℝ)*(major2) + (598772938158153/10000000000000 : ℝ)*(sp0) + (5987764956677887/100000000000000 : ℝ)*(sp1) + (5987765115473909/100000000000000 : ℝ)*(sp2) + (2836264955572657/100000000000000 : ℝ)*(sp3) + (37142071769/100000000000000 : ℝ)*(sp4) + (950212169/6250000000000 : ℝ)*(sp7) + (2836280158967361/100000000000000 : ℝ)*(f.failure) + (5987766523653299/100000000000000 : ℝ)*(f.sum) + (38807983159/9406250000000000000000000 : ℝ)*base65 + (40157052254300111/7525000000000000000000000000000 : ℝ)*base68 + (71358196830799889/7525000000000000000000000000000 : ℝ)*base69 + (66831885770024889/7525000000000000000000000000000 : ℝ)*base71 + (1668332879013/301000000000000000000000000 : ℝ)*base74 + (13790773268050111/7525000000000000000000000000000 : ℝ)*base76 + (43966841387424889/7525000000000000000000000000000 : ℝ)*base77 + (26627106799400111/7525000000000000000000000000000 : ℝ)*base80 + (77618603851/18812500000000000000000000 : ℝ)*base82 + (18293007/10000000000000000000000 : ℝ)*base89 + (18293007/10000000000000000000000 : ℝ)*base91 + (18293007/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (667947015906261746729869281/75250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (724463847/100000000000000 : ℝ)*(base19) + (370755407/50000000000000 : ℝ)*(base23) + (223216401/100000000000000 : ℝ)*(upper3) + (2090291/3125000000000 : ℝ)*(lower4) + (63403549/100000000000000 : ℝ)*(upper5) + (2222025378138243/50000000000000 : ℝ)*(major0) + (2222025378138243/50000000000000 : ℝ)*(major1) + (2222025378138243/50000000000000 : ℝ)*(major2) + (440688979/3125000000000 : ℝ)*(sp1) + (22926540723/100000000000000 : ℝ)*(sp2) + (6031232224422539/100000000000000 : ℝ)*(sp4) + (1507804349477841/25000000000000 : ℝ)*(sp5) + (3015604278185501/50000000000000 : ℝ)*(sp6) + (2856868992251349/100000000000000 : ℝ)*(sp7) + (2856868992251349/100000000000000 : ℝ)*(f.failure) + (6031232224422539/100000000000000 : ℝ)*(f.sum) + (703655074427/602000000000000000000000000 : ℝ)*base66 + (315808097096668573/150500000000000000000000000000000 : ℝ)*base67 + (884653953339668573/150500000000000000000000000000000 : ℝ)*base69 + (937721924943168573/150500000000000000000000000000000 : ℝ)*base71 + (2207044350129/602000000000000000000000000 : ℝ)*base73 + (439805866346831427/150500000000000000000000000000000 : ℝ)*base76 + (1020494120827168573/150500000000000000000000000000000 : ℝ)*base77 + (59741062028331427/150500000000000000000000000000000 : ℝ)*base80 + (2157652148837/602000000000000000000000000 : ℝ)*base81 + (78279237/10000000000000000000000 : ℝ)*base90 + (78279237/10000000000000000000000 : ℝ)*base92 + (78279237/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1363_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1363_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1363_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1363_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1363_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1363_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
