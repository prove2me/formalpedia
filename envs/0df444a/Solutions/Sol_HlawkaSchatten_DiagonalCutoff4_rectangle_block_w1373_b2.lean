-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1373_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:23.188018+00:00
-- url     : https://prove2.me/submissions/92883a89-7932-4c6b-ba1a-ff7b689abf51

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
theorem support_rectangle_w1373_s6_0 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50437219/250000000 : ℝ)*x 0 + (2705557559/5000000000 : ℝ)*x 1 + (2622752209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50437219/250000000 : ℝ)^4333 ≤ (12293587420951/100000000000000 : ℝ)^3309 := by
    have hnat : (50437219 : ℕ)^4333*100000000000000^3309 ≤ 12293587420951^3309*250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50437219 250000000 12293587420951 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705557559/5000000000 : ℝ)^4333 ≤ (8949112074329/20000000000000 : ℝ)^3309 := by
    have hnat : (2705557559 : ℕ)^4333*20000000000000^3309 ≤ 8949112074329^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705557559 5000000000 8949112074329 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622752209/5000000000 : ℝ)^4333 ≤ (21480426095797/50000000000000 : ℝ)^3309 := by
    have hnat : (2622752209 : ℕ)^4333*50000000000000^3309 ≤ 21480426095797^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622752209 5000000000 21480426095797 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50437219/250000000 : ℝ), (2705557559/5000000000 : ℝ), (2622752209/5000000000 : ℝ)] ![(12293587420951/100000000000000 : ℝ), (8949112074329/20000000000000 : ℝ), (21480426095797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50437219/250000000 : ℝ)|^4333 ≤ (12293587420951/100000000000000 : ℝ)^3309
        have hw : |(-50437219/250000000 : ℝ)|=(50437219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705557559/5000000000 : ℝ)|^4333 ≤ (8949112074329/20000000000000 : ℝ)^3309
        have hw : |(2705557559/5000000000 : ℝ)|=(2705557559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622752209/5000000000 : ℝ)|^4333 ≤ (21480426095797/50000000000000 : ℝ)^3309
        have hw : |(2622752209/5000000000 : ℝ)|=(2622752209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s6_1 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337110741/2500000000 : ℝ)*x 0 + (-262730481/1250000000 : ℝ)*x 1 + (1049100991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337110741/2500000000 : ℝ)^4333 ≤ (1101703874963/2500000000000 : ℝ)^3309 := by
    have hnat : (1337110741 : ℕ)^4333*2500000000000^3309 ≤ 1101703874963^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337110741 2500000000 1101703874963 2500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262730481/1250000000 : ℝ)^4333 ≤ (12970987037487/100000000000000 : ℝ)^3309 := by
    have hnat : (262730481 : ℕ)^4333*100000000000000^3309 ≤ 12970987037487^3309*1250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262730481 1250000000 12970987037487 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049100991/2000000000 : ℝ)^4333 ≤ (42960857950657/100000000000000 : ℝ)^3309 := by
    have hnat : (1049100991 : ℕ)^4333*100000000000000^3309 ≤ 42960857950657^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049100991 2000000000 42960857950657 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337110741/2500000000 : ℝ), (-262730481/1250000000 : ℝ), (1049100991/2000000000 : ℝ)] ![(1101703874963/2500000000000 : ℝ), (12970987037487/100000000000000 : ℝ), (42960857950657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337110741/2500000000 : ℝ)|^4333 ≤ (1101703874963/2500000000000 : ℝ)^3309
        have hw : |(1337110741/2500000000 : ℝ)|=(1337110741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262730481/1250000000 : ℝ)|^4333 ≤ (12970987037487/100000000000000 : ℝ)^3309
        have hw : |(-262730481/1250000000 : ℝ)|=(262730481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049100991/2000000000 : ℝ)|^4333 ≤ (42960857950657/100000000000000 : ℝ)^3309
        have hw : |(1049100991/2000000000 : ℝ)|=(1049100991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s6_2 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534844299/1000000000 : ℝ)*x 0 + (5245504971/10000000000 : ℝ)*x 1 + (-131365237/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534844299/1000000000 : ℝ)^4333 ≤ (137712985247/312500000000 : ℝ)^3309 := by
    have hnat : (534844299 : ℕ)^4333*312500000000^3309 ≤ 137712985247^3309*1000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534844299 1000000000 137712985247 312500000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245504971/10000000000 : ℝ)^4333 ≤ (171843432489/400000000000 : ℝ)^3309 := by
    have hnat : (5245504971 : ℕ)^4333*400000000000^3309 ≤ 171843432489^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245504971 10000000000 171843432489 400000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131365237/625000000 : ℝ)^4333 ≤ (12970986584951/100000000000000 : ℝ)^3309 := by
    have hnat : (131365237 : ℕ)^4333*100000000000000^3309 ≤ 12970986584951^3309*625000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131365237 625000000 12970986584951 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534844299/1000000000 : ℝ), (5245504971/10000000000 : ℝ), (-131365237/625000000 : ℝ)] ![(137712985247/312500000000 : ℝ), (171843432489/400000000000 : ℝ), (12970986584951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534844299/1000000000 : ℝ)|^4333 ≤ (137712985247/312500000000 : ℝ)^3309
        have hw : |(534844299/1000000000 : ℝ)|=(534844299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245504971/10000000000 : ℝ)|^4333 ≤ (171843432489/400000000000 : ℝ)^3309
        have hw : |(5245504971/10000000000 : ℝ)|=(5245504971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131365237/625000000 : ℝ)|^4333 ≤ (12970986584951/100000000000000 : ℝ)^3309
        have hw : |(-131365237/625000000 : ℝ)|=(131365237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s6_3 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318577143/10000000000 : ℝ)*x 0 + (4146398677/10000000000 : ℝ)*x 1 + (2248664307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318577143/10000000000 : ℝ)^4333 ≤ (16651891007053/50000000000000 : ℝ)^3309 := by
    have hnat : (4318577143 : ℕ)^4333*50000000000000^3309 ≤ 16651891007053^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318577143 10000000000 16651891007053 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4146398677/10000000000 : ℝ)^4333 ≤ (31575912174749/100000000000000 : ℝ)^3309 := by
    have hnat : (4146398677 : ℕ)^4333*100000000000000^3309 ≤ 31575912174749^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146398677 10000000000 31575912174749 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248664307/5000000000 : ℝ)^4333 ≤ (35120305798753/100000000000000 : ℝ)^3309 := by
    have hnat : (2248664307 : ℕ)^4333*100000000000000^3309 ≤ 35120305798753^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248664307 5000000000 35120305798753 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318577143/10000000000 : ℝ), (4146398677/10000000000 : ℝ), (2248664307/5000000000 : ℝ)] ![(16651891007053/50000000000000 : ℝ), (31575912174749/100000000000000 : ℝ), (35120305798753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318577143/10000000000 : ℝ)|^4333 ≤ (16651891007053/50000000000000 : ℝ)^3309
        have hw : |(4318577143/10000000000 : ℝ)|=(4318577143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4146398677/10000000000 : ℝ)|^4333 ≤ (31575912174749/100000000000000 : ℝ)^3309
        have hw : |(4146398677/10000000000 : ℝ)|=(4146398677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248664307/5000000000 : ℝ)|^4333 ≤ (35120305798753/100000000000000 : ℝ)^3309
        have hw : |(2248664307/5000000000 : ℝ)|=(2248664307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s6_4 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-126093769/625000000 : ℝ)*x 0 + (163940613/312500000 : ℝ)*x 1 + (5410517091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126093769/625000000 : ℝ)^4333 ≤ (2458735906587/20000000000000 : ℝ)^3309 := by
    have hnat : (126093769 : ℕ)^4333*20000000000000^3309 ≤ 2458735906587^3309*625000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126093769 625000000 2458735906587 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163940613/312500000 : ℝ)^4333 ≤ (42967235511943/100000000000000 : ℝ)^3309 := by
    have hnat : (163940613 : ℕ)^4333*100000000000000^3309 ≤ 42967235511943^3309*312500000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163940613 312500000 42967235511943 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410517091/10000000000 : ℝ)^4333 ≤ (44739084943849/100000000000000 : ℝ)^3309 := by
    have hnat : (5410517091 : ℕ)^4333*100000000000000^3309 ≤ 44739084943849^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410517091 10000000000 44739084943849 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126093769/625000000 : ℝ), (163940613/312500000 : ℝ), (5410517091/10000000000 : ℝ)] ![(2458735906587/20000000000000 : ℝ), (42967235511943/100000000000000 : ℝ), (44739084943849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126093769/625000000 : ℝ)|^4333 ≤ (2458735906587/20000000000000 : ℝ)^3309
        have hw : |(-126093769/625000000 : ℝ)|=(126093769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163940613/312500000 : ℝ)|^4333 ≤ (42967235511943/100000000000000 : ℝ)^3309
        have hw : |(163940613/312500000 : ℝ)|=(163940613/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410517091/10000000000 : ℝ)|^4333 ≤ (44739084943849/100000000000000 : ℝ)^3309
        have hw : |(5410517091/10000000000 : ℝ)|=(5410517091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s6_5 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305637077/10000000000 : ℝ)*x 0 + (-968415957/5000000000 : ℝ)*x 1 + (2705258543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305637077/10000000000 : ℝ)^4333 ≤ (43606886519997/100000000000000 : ℝ)^3309 := by
    have hnat : (5305637077 : ℕ)^4333*100000000000000^3309 ≤ 43606886519997^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305637077 10000000000 43606886519997 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (968415957/5000000000 : ℝ)^4333 ≤ (11654028571521/100000000000000 : ℝ)^3309 := by
    have hnat : (968415957 : ℕ)^4333*100000000000000^3309 ≤ 11654028571521^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968415957 5000000000 11654028571521 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705258543/5000000000 : ℝ)^4333 ≤ (4473908488971/10000000000000 : ℝ)^3309 := by
    have hnat : (2705258543 : ℕ)^4333*10000000000000^3309 ≤ 4473908488971^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705258543 5000000000 4473908488971 10000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305637077/10000000000 : ℝ), (-968415957/5000000000 : ℝ), (2705258543/5000000000 : ℝ)] ![(43606886519997/100000000000000 : ℝ), (11654028571521/100000000000000 : ℝ), (4473908488971/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305637077/10000000000 : ℝ)|^4333 ≤ (43606886519997/100000000000000 : ℝ)^3309
        have hw : |(5305637077/10000000000 : ℝ)|=(5305637077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-968415957/5000000000 : ℝ)|^4333 ≤ (11654028571521/100000000000000 : ℝ)^3309
        have hw : |(-968415957/5000000000 : ℝ)|=(968415957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705258543/5000000000 : ℝ)|^4333 ≤ (4473908488971/10000000000000 : ℝ)^3309
        have hw : |(2705258543/5000000000 : ℝ)|=(2705258543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s6_6 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305637091/10000000000 : ℝ)*x 0 + (216420683/400000000 : ℝ)*x 1 + (-1936831911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305637091/10000000000 : ℝ)^4333 ≤ (43606886670671/100000000000000 : ℝ)^3309 := by
    have hnat : (5305637091 : ℕ)^4333*100000000000000^3309 ≤ 43606886670671^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305637091 10000000000 43606886670671 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216420683/400000000 : ℝ)^4333 ≤ (11184771192651/25000000000000 : ℝ)^3309 := by
    have hnat : (216420683 : ℕ)^4333*25000000000000^3309 ≤ 11184771192651^3309*400000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216420683 400000000 11184771192651 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936831911/10000000000 : ℝ)^4333 ≤ (2913507136971/25000000000000 : ℝ)^3309 := by
    have hnat : (1936831911 : ℕ)^4333*25000000000000^3309 ≤ 2913507136971^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936831911 10000000000 2913507136971 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305637091/10000000000 : ℝ), (216420683/400000000 : ℝ), (-1936831911/10000000000 : ℝ)] ![(43606886670671/100000000000000 : ℝ), (11184771192651/25000000000000 : ℝ), (2913507136971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305637091/10000000000 : ℝ)|^4333 ≤ (43606886670671/100000000000000 : ℝ)^3309
        have hw : |(5305637091/10000000000 : ℝ)|=(5305637091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216420683/400000000 : ℝ)|^4333 ≤ (11184771192651/25000000000000 : ℝ)^3309
        have hw : |(216420683/400000000 : ℝ)|=(216420683/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1936831911/10000000000 : ℝ)|^4333 ≤ (2913507136971/25000000000000 : ℝ)^3309
        have hw : |(-1936831911/10000000000 : ℝ)|=(1936831911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s6_7 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318602689/10000000000 : ℝ)*x 0 + (4496069303/10000000000 : ℝ)*x 1 + (829532813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318602689/10000000000 : ℝ)^4333 ≤ (666080799669/2000000000000 : ℝ)^3309 := by
    have hnat : (4318602689 : ℕ)^4333*2000000000000^3309 ≤ 666080799669^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318602689 10000000000 666080799669 2000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496069303/10000000000 : ℝ)^4333 ≤ (8776857236219/25000000000000 : ℝ)^3309 := by
    have hnat : (4496069303 : ℕ)^4333*25000000000000^3309 ≤ 8776857236219^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496069303 10000000000 8776857236219 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829532813/2000000000 : ℝ)^4333 ≤ (31588531059883/100000000000000 : ℝ)^3309 := by
    have hnat : (829532813 : ℕ)^4333*100000000000000^3309 ≤ 31588531059883^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829532813 2000000000 31588531059883 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318602689/10000000000 : ℝ), (4496069303/10000000000 : ℝ), (829532813/2000000000 : ℝ)] ![(666080799669/2000000000000 : ℝ), (8776857236219/25000000000000 : ℝ), (31588531059883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318602689/10000000000 : ℝ)|^4333 ≤ (666080799669/2000000000000 : ℝ)^3309
        have hw : |(4318602689/10000000000 : ℝ)|=(4318602689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496069303/10000000000 : ℝ)|^4333 ≤ (8776857236219/25000000000000 : ℝ)^3309
        have hw : |(4496069303/10000000000 : ℝ)|=(4496069303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829532813/2000000000 : ℝ)|^4333 ≤ (31588531059883/100000000000000 : ℝ)^3309
        have hw : |(829532813/2000000000 : ℝ)|=(829532813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1373_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (561/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7363/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (1083/256 : ℝ) ≤ (9550843069722821/100000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^1083 ≤ (9550843069722821/100000000000000000000 : ℝ)^256 := by
      have hnat : (5607 : ℕ)^1083*100000000000000000000^256 ≤ 9550843069722821^256*50000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 9550843069722821 100000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (9550843069722821/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3683/25000 : ℝ) ^ (1083/256 : ℝ) ≤ (1211761494619933/4000000000000000000 : ℝ) := by
    have hpowers : (3683/25000 : ℝ)^1083 ≤ (1211761494619933/4000000000000000000 : ℝ)^256 := by
      have hnat : (3683 : ℕ)^1083*4000000000000000000^256 ≤ 1211761494619933^256*25000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3683 25000 1211761494619933 4000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3683/25000 : ℝ)) (X := (1211761494619933/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009550843069722821/50000000000000000000 : ℝ) ≤ (5000225746770611/5000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (50009550843069722821/50000000000000000000 : ℝ)^256 ≤ (5000225746770611/5000000000000000 : ℝ)^1083 := by
      have hnat : (50009550843069722821 : ℕ)^256*5000000000000000^1083 ≤ 5000225746770611^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009550843069722821 50000000000000000000 5000225746770611 5000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000225746770611/5000000000000000 : ℝ)) (X := (50009550843069722821/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019922440217610573/50000000000000000000 : ℝ) ≤ (10000941711723723/10000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (50019922440217610573/50000000000000000000 : ℝ)^256 ≤ (10000941711723723/10000000000000000 : ℝ)^1083 := by
      have hnat : (50019922440217610573 : ℕ)^256*10000000000000000^1083 ≤ 10000941711723723^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019922440217610573 50000000000000000000 10000941711723723 10000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000941711723723/10000000000000000 : ℝ)) (X := (50019922440217610573/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001211761494619933/2000000000000000000 : ℝ) ≤ (625089495619139/625000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (2001211761494619933/2000000000000000000 : ℝ)^256 ≤ (625089495619139/625000000000000 : ℝ)^1083 := by
      have hnat : (2001211761494619933 : ℕ)^256*625000000000000^1083 ≤ 625089495619139^1083*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001211761494619933 2000000000000000000 625089495619139 625000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625089495619139/625000000000000 : ℝ)) (X := (2001211761494619933/2000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9550843069722821/100000000000000000000 : ℝ) ≤ ((4396324217610110821/4397500000000000000 : ℝ)+2*(490218182501/351800000000000 : ℝ)*(5607/50000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (4396324217610110821/4397500000000000000 : ℝ)+2*(490218182501/351800000000000 : ℝ)*(5607/50000 : ℝ)=(5000225746770611/5000000000000000 : ℝ) by norm_num, show 1+2*(9550843069722821/100000000000000000000 : ℝ)=(50009550843069722821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1211761494619933/4000000000000000000 : ℝ)+(9550843069722821/100000000000000000000 : ℝ) ≤ ((4396324217610110821/4397500000000000000 : ℝ)+(490218182501/351800000000000 : ℝ)*((3683/25000 : ℝ)+(5607/50000 : ℝ)))^(1083/256 : ℝ) := by
    rw [show (4396324217610110821/4397500000000000000 : ℝ)+(490218182501/351800000000000 : ℝ)*((3683/25000 : ℝ)+(5607/50000 : ℝ))=(10000941711723723/10000000000000000 : ℝ) by norm_num, show 1+(1211761494619933/4000000000000000000 : ℝ)+(9550843069722821/100000000000000000000 : ℝ)=(50019922440217610573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1211761494619933/4000000000000000000 : ℝ) ≤ ((4396324217610110821/4397500000000000000 : ℝ)+2*(490218182501/351800000000000 : ℝ)*(3683/25000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (4396324217610110821/4397500000000000000 : ℝ)+2*(490218182501/351800000000000 : ℝ)*(3683/25000 : ℝ)=(625089495619139/625000000000000 : ℝ) by norm_num, show 1+2*(1211761494619933/4000000000000000000 : ℝ)=(2001211761494619933/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4396324217610110821/4397500000000000000 : ℝ)*(X 1 0+X 2 0)+(490218182501/351800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (4396324217610110821/4397500000000000000 : ℝ)) (alpha := (490218182501/351800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4396324217610110821/4397500000000000000 : ℝ)*(X 0 1+X 2 1)+(490218182501/351800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (4396324217610110821/4397500000000000000 : ℝ)) (alpha := (490218182501/351800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4396324217610110821/4397500000000000000 : ℝ)*(X 0 2+X 1 2)+(490218182501/351800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (4396324217610110821/4397500000000000000 : ℝ)) (alpha := (490218182501/351800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-50437219/250000000 : ℝ)*X 0 0+(2705557559/5000000000 : ℝ)*X 0 1+(2622752209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337110741/2500000000 : ℝ)*X 1 0+(-262730481/1250000000 : ℝ)*X 1 1+(1049100991/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534844299/1000000000 : ℝ)*X 2 0+(5245504971/10000000000 : ℝ)*X 2 1+(-131365237/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318577143/10000000000 : ℝ)*X 0 0+(4146398677/10000000000 : ℝ)*X 0 1+(2248664307/5000000000 : ℝ)*X 0 2+(4318577143/10000000000 : ℝ)*X 1 0+(4146398677/10000000000 : ℝ)*X 1 1+(2248664307/5000000000 : ℝ)*X 1 2+(4318577143/10000000000 : ℝ)*X 2 0+(4146398677/10000000000 : ℝ)*X 2 1+(2248664307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-126093769/625000000 : ℝ)*X 0 0+(163940613/312500000 : ℝ)*X 0 1+(5410517091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305637077/10000000000 : ℝ)*X 1 0+(-968415957/5000000000 : ℝ)*X 1 1+(2705258543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305637091/10000000000 : ℝ)*X 2 0+(216420683/400000000 : ℝ)*X 2 1+(-1936831911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318602689/10000000000 : ℝ)*X 0 0+(4496069303/10000000000 : ℝ)*X 0 1+(829532813/2000000000 : ℝ)*X 0 2+(4318602689/10000000000 : ℝ)*X 1 0+(4496069303/10000000000 : ℝ)*X 1 1+(829532813/2000000000 : ℝ)*X 1 2+(4318602689/10000000000 : ℝ)*X 2 0+(4496069303/10000000000 : ℝ)*X 2 1+(829532813/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177209111767680612998277717/54968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (757688951/50000000000000 : ℝ)*(base19) + (566984639/50000000000000 : ℝ)*(base23) + (32537733/100000000000000 : ℝ)*(upper2) + (217743093/100000000000000 : ℝ)*(upper3) + (126115847/50000000000000 : ℝ)*(upper4) + (1110993621891109/25000000000000 : ℝ)*(major0) + (1110993621891109/25000000000000 : ℝ)*(major1) + (1110993621891109/25000000000000 : ℝ)*(major2) + (3019154863889989/50000000000000 : ℝ)*(sp0) + (3019179164958271/50000000000000 : ℝ)*(sp1) + (1207671742265033/20000000000000 : ℝ)*(sp2) + (1424788927301359/50000000000000 : ℝ)*(sp3) + (25058757233/50000000000000 : ℝ)*(sp4) + (697985699/6250000000000 : ℝ)*(sp7) + (1424794511186951/50000000000000 : ℝ)*(f.failure) + (6038359845294443/100000000000000 : ℝ)*(f.sum) + (7658444892013/2198750000000000000000000000 : ℝ)*base66 + (1170940705569172011/109937500000000000000000000000000 : ℝ)*base68 + (196040870476422011/109937500000000000000000000000000 : ℝ)*base70 + (1524189422366672011/109937500000000000000000000000000 : ℝ)*base72 + (687379287821/274843750000000000000000000 : ℝ)*base74 + (980311292951422011/109937500000000000000000000000000 : ℝ)*base76 + (390071696117202989/109937500000000000000000000000000 : ℝ)*base77 + (91763737803015489/109937500000000000000000000000000 : ℝ)*base79 + (9697353671861/4397500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (35773259/2500000000000000000000 : ℝ)*base89 + (35773259/2500000000000000000000 : ℝ)*base91 + (35773259/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (167713517757278271136315659/54968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (263206721/50000000000000 : ℝ)*(base19) + (29566843/5000000000000 : ℝ)*(base23) + (58234261/100000000000000 : ℝ)*(upper3) + (22993489/100000000000000 : ℝ)*(lower4) + (72634467/100000000000000 : ℝ)*(upper5) + (1119037426314543/25000000000000 : ℝ)*(major0) + (1119037426314543/25000000000000 : ℝ)*(major1) + (1119037426314543/25000000000000 : ℝ)*(major2) + (5463878523/50000000000000 : ℝ)*(sp1) + (2903504321/25000000000000 : ℝ)*(sp2) + (608207872174747/10000000000000 : ℝ)*(sp4) + (6082067267576981/100000000000000 : ℝ)*(sp5) + (3041033258196663/50000000000000 : ℝ)*(sp6) + (1435110293533263/50000000000000 : ℝ)*(sp7) + (1435110293533263/50000000000000 : ℝ)*(f.failure) + (608207872174747/10000000000000 : ℝ)*(f.sum) + (6912322203139/2198750000000000000000000000 : ℝ)*base65 + (224248250864367697/109937500000000000000000000000000 : ℝ)*base68 + (987529590757007303/109937500000000000000000000000000 : ℝ)*base69 + (1221131460115444803/109937500000000000000000000000000 : ℝ)*base71 + (16394400409517/4397500000000000000000000000 : ℝ)*base74 + (279934407695117697/109937500000000000000000000000000 : ℝ)*base76 + (207357381025492697/109937500000000000000000000000000 : ℝ)*base78 + (1436307945410992697/109937500000000000000000000000000 : ℝ)*base80 + (9405140450833/4397500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2491533/2500000000000000000000 : ℝ)*base90 + (2491533/2500000000000000000000 : ℝ)*base92 + (2491533/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1373_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1373_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1373_s7_0 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-504373253/2500000000 : ℝ)*x 0 + (2705533711/5000000000 : ℝ)*x 1 + (5245549411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504373253/2500000000 : ℝ)^4333 ≤ (12293621348527/100000000000000 : ℝ)^3309 := by
    have hnat : (504373253 : ℕ)^4333*100000000000000^3309 ≤ 12293621348527^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504373253 2500000000 12293621348527 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705533711/5000000000 : ℝ)^4333 ≤ (5593130488989/12500000000000 : ℝ)^3309 := by
    have hnat : (2705533711 : ℕ)^4333*12500000000000^3309 ≤ 5593130488989^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705533711 5000000000 5593130488989 12500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245549411/10000000000 : ℝ)^4333 ≤ (42961334720217/100000000000000 : ℝ)^3309 := by
    have hnat : (5245549411 : ℕ)^4333*100000000000000^3309 ≤ 42961334720217^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245549411 10000000000 42961334720217 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504373253/2500000000 : ℝ), (2705533711/5000000000 : ℝ), (5245549411/10000000000 : ℝ)] ![(12293621348527/100000000000000 : ℝ), (5593130488989/12500000000000 : ℝ), (42961334720217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504373253/2500000000 : ℝ)|^4333 ≤ (12293621348527/100000000000000 : ℝ)^3309
        have hw : |(-504373253/2500000000 : ℝ)|=(504373253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705533711/5000000000 : ℝ)|^4333 ≤ (5593130488989/12500000000000 : ℝ)^3309
        have hw : |(2705533711/5000000000 : ℝ)|=(2705533711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245549411/10000000000 : ℝ)|^4333 ≤ (42961334720217/100000000000000 : ℝ)^3309
        have hw : |(5245549411/10000000000 : ℝ)|=(5245549411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s7_1 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348430859/10000000000 : ℝ)*x 0 + (-410508/1953125 : ℝ)*x 1 + (5245549449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348430859/10000000000 : ℝ)^4333 ≤ (44068024395247/100000000000000 : ℝ)^3309 := by
    have hnat : (5348430859 : ℕ)^4333*100000000000000^3309 ≤ 44068024395247^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348430859 10000000000 44068024395247 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410508/1953125 : ℝ)^4333 ≤ (6485320230569/50000000000000 : ℝ)^3309 := by
    have hnat : (410508 : ℕ)^4333*50000000000000^3309 ≤ 6485320230569^3309*1953125^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410508 1953125 6485320230569 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245549449/10000000000 : ℝ)^4333 ≤ (171845340511/400000000000 : ℝ)^3309 := by
    have hnat : (5245549449 : ℕ)^4333*400000000000^3309 ≤ 171845340511^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245549449 10000000000 171845340511 400000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348430859/10000000000 : ℝ), (-410508/1953125 : ℝ), (5245549449/10000000000 : ℝ)] ![(44068024395247/100000000000000 : ℝ), (6485320230569/50000000000000 : ℝ), (171845340511/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348430859/10000000000 : ℝ)|^4333 ≤ (44068024395247/100000000000000 : ℝ)^3309
        have hw : |(5348430859/10000000000 : ℝ)|=(5348430859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410508/1953125 : ℝ)|^4333 ≤ (6485320230569/50000000000000 : ℝ)^3309
        have hw : |(-410508/1953125 : ℝ)|=(410508/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245549449/10000000000 : ℝ)|^4333 ≤ (171845340511/400000000000 : ℝ)^3309
        have hw : |(5245549449/10000000000 : ℝ)|=(5245549449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s7_2 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069686177/2000000000 : ℝ)*x 0 + (1049109887/2000000000 : ℝ)*x 1 + (-2101800943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069686177/2000000000 : ℝ)^4333 ≤ (22034012337883/50000000000000 : ℝ)^3309 := by
    have hnat : (1069686177 : ℕ)^4333*50000000000000^3309 ≤ 22034012337883^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069686177 2000000000 22034012337883 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049109887/2000000000 : ℝ)^4333 ≤ (21480667488803/50000000000000 : ℝ)^3309 := by
    have hnat : (1049109887 : ℕ)^4333*50000000000000^3309 ≤ 21480667488803^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049109887 2000000000 21480667488803 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101800943/10000000000 : ℝ)^4333 ≤ (6485320161881/50000000000000 : ℝ)^3309 := by
    have hnat : (2101800943 : ℕ)^4333*50000000000000^3309 ≤ 6485320161881^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101800943 10000000000 6485320161881 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069686177/2000000000 : ℝ), (1049109887/2000000000 : ℝ), (-2101800943/10000000000 : ℝ)] ![(22034012337883/50000000000000 : ℝ), (21480667488803/50000000000000 : ℝ), (6485320161881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069686177/2000000000 : ℝ)|^4333 ≤ (22034012337883/50000000000000 : ℝ)^3309
        have hw : |(1069686177/2000000000 : ℝ)|=(1069686177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049109887/2000000000 : ℝ)|^4333 ≤ (21480667488803/50000000000000 : ℝ)^3309
        have hw : |(1049109887/2000000000 : ℝ)|=(1049109887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2101800943/10000000000 : ℝ)|^4333 ≤ (6485320161881/50000000000000 : ℝ)^3309
        have hw : |(-2101800943/10000000000 : ℝ)|=(2101800943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s7_3 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318580783/10000000000 : ℝ)*x 0 + (259155899/625000000 : ℝ)*x 1 + (4497231687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318580783/10000000000 : ℝ)^4333 ≤ (8325954692907/25000000000000 : ℝ)^3309 := by
    have hnat : (4318580783 : ℕ)^4333*25000000000000^3309 ≤ 8325954692907^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318580783 10000000000 8325954692907 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259155899/625000000 : ℝ)^4333 ≤ (7894216639069/25000000000000 : ℝ)^3309 := by
    have hnat : (259155899 : ℕ)^4333*25000000000000^3309 ≤ 7894216639069^3309*625000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259155899 625000000 7894216639069 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497231687/10000000000 : ℝ)^4333 ≤ (7023862929967/20000000000000 : ℝ)^3309 := by
    have hnat : (4497231687 : ℕ)^4333*20000000000000^3309 ≤ 7023862929967^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497231687 10000000000 7023862929967 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318580783/10000000000 : ℝ), (259155899/625000000 : ℝ), (4497231687/10000000000 : ℝ)] ![(8325954692907/25000000000000 : ℝ), (7894216639069/25000000000000 : ℝ), (7023862929967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318580783/10000000000 : ℝ)|^4333 ≤ (8325954692907/25000000000000 : ℝ)^3309
        have hw : |(4318580783/10000000000 : ℝ)|=(4318580783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259155899/625000000 : ℝ)|^4333 ≤ (7894216639069/25000000000000 : ℝ)^3309
        have hw : |(259155899/625000000 : ℝ)|=(259155899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497231687/10000000000 : ℝ)|^4333 ≤ (7023862929967/20000000000000 : ℝ)^3309
        have hw : |(4497231687/10000000000 : ℝ)|=(4497231687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s7_4 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-201750497/1000000000 : ℝ)*x 0 + (524614303/1000000000 : ℝ)*x 1 + (5410470651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201750497/1000000000 : ℝ)^4333 ≤ (192089324437/1562500000000 : ℝ)^3309 := by
    have hnat : (201750497 : ℕ)^4333*1562500000000^3309 ≤ 192089324437^3309*1000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201750497 1000000000 192089324437 1562500000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524614303/1000000000 : ℝ)^4333 ≤ (8593540224573/20000000000000 : ℝ)^3309 := by
    have hnat : (524614303 : ℕ)^4333*20000000000000^3309 ≤ 8593540224573^3309*1000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524614303 1000000000 8593540224573 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410470651/10000000000 : ℝ)^4333 ≤ (44738582101461/100000000000000 : ℝ)^3309 := by
    have hnat : (5410470651 : ℕ)^4333*100000000000000^3309 ≤ 44738582101461^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410470651 10000000000 44738582101461 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201750497/1000000000 : ℝ), (524614303/1000000000 : ℝ), (5410470651/10000000000 : ℝ)] ![(192089324437/1562500000000 : ℝ), (8593540224573/20000000000000 : ℝ), (44738582101461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201750497/1000000000 : ℝ)|^4333 ≤ (192089324437/1562500000000 : ℝ)^3309
        have hw : |(-201750497/1000000000 : ℝ)|=(201750497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524614303/1000000000 : ℝ)|^4333 ≤ (8593540224573/20000000000000 : ℝ)^3309
        have hw : |(524614303/1000000000 : ℝ)|=(524614303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410470651/10000000000 : ℝ)|^4333 ≤ (44738582101461/100000000000000 : ℝ)^3309
        have hw : |(5410470651/10000000000 : ℝ)|=(5410470651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s7_5 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305649223/10000000000 : ℝ)*x 0 + (-484219927/2500000000 : ℝ)*x 1 + (1082094047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305649223/10000000000 : ℝ)^4333 ≤ (21803508620127/50000000000000 : ℝ)^3309 := by
    have hnat : (5305649223 : ℕ)^4333*50000000000000^3309 ≤ 21803508620127^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305649223 10000000000 21803508620127 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484219927/2500000000 : ℝ)^4333 ≤ (728400321637/6250000000000 : ℝ)^3309 := by
    have hnat : (484219927 : ℕ)^4333*6250000000000^3309 ≤ 728400321637^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484219927 2500000000 728400321637 6250000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082094047/2000000000 : ℝ)^4333 ≤ (11184644399277/25000000000000 : ℝ)^3309 := by
    have hnat : (1082094047 : ℕ)^4333*25000000000000^3309 ≤ 11184644399277^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082094047 2000000000 11184644399277 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305649223/10000000000 : ℝ), (-484219927/2500000000 : ℝ), (1082094047/2000000000 : ℝ)] ![(21803508620127/50000000000000 : ℝ), (728400321637/6250000000000 : ℝ), (11184644399277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305649223/10000000000 : ℝ)|^4333 ≤ (21803508620127/50000000000000 : ℝ)^3309
        have hw : |(5305649223/10000000000 : ℝ)|=(5305649223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484219927/2500000000 : ℝ)|^4333 ≤ (728400321637/6250000000000 : ℝ)^3309
        have hw : |(-484219927/2500000000 : ℝ)|=(484219927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082094047/2000000000 : ℝ)|^4333 ≤ (11184644399277/25000000000000 : ℝ)^3309
        have hw : |(1082094047/2000000000 : ℝ)|=(1082094047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s7_6 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663206123/1250000000 : ℝ)*x 0 + (676308803/1250000000 : ℝ)*x 1 + (-968439887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663206123/1250000000 : ℝ)^4333 ≤ (43607014668037/100000000000000 : ℝ)^3309 := by
    have hnat : (663206123 : ℕ)^4333*100000000000000^3309 ≤ 43607014668037^3309*1250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663206123 1250000000 43607014668037 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676308803/1250000000 : ℝ)^4333 ≤ (44738579643557/100000000000000 : ℝ)^3309 := by
    have hnat : (676308803 : ℕ)^4333*100000000000000^3309 ≤ 44738579643557^3309*1250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676308803 1250000000 44738579643557 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968439887/5000000000 : ℝ)^4333 ≤ (1456800708277/12500000000000 : ℝ)^3309 := by
    have hnat : (968439887 : ℕ)^4333*12500000000000^3309 ≤ 1456800708277^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968439887 5000000000 1456800708277 12500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663206123/1250000000 : ℝ), (676308803/1250000000 : ℝ), (-968439887/5000000000 : ℝ)] ![(43607014668037/100000000000000 : ℝ), (44738579643557/100000000000000 : ℝ), (1456800708277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663206123/1250000000 : ℝ)|^4333 ≤ (43607014668037/100000000000000 : ℝ)^3309
        have hw : |(663206123/1250000000 : ℝ)|=(663206123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676308803/1250000000 : ℝ)|^4333 ≤ (44738579643557/100000000000000 : ℝ)^3309
        have hw : |(676308803/1250000000 : ℝ)|=(676308803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-968439887/5000000000 : ℝ)|^4333 ≤ (1456800708277/12500000000000 : ℝ)^3309
        have hw : |(-968439887/5000000000 : ℝ)|=(968439887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_s7_7 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863721169/2000000000 : ℝ)*x 0 + (4495973451/10000000000 : ℝ)*x 1 + (4147759143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863721169/2000000000 : ℝ)^4333 ≤ (8326017963373/25000000000000 : ℝ)^3309 := by
    have hnat : (863721169 : ℕ)^4333*25000000000000^3309 ≤ 8326017963373^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863721169 2000000000 8326017963373 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495973451/10000000000 : ℝ)^4333 ≤ (35106448873519/100000000000000 : ℝ)^3309 := by
    have hnat : (4495973451 : ℕ)^4333*100000000000000^3309 ≤ 35106448873519^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495973451 10000000000 35106448873519 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147759143/10000000000 : ℝ)^4333 ≤ (15794739629293/50000000000000 : ℝ)^3309 := by
    have hnat : (4147759143 : ℕ)^4333*50000000000000^3309 ≤ 15794739629293^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147759143 10000000000 15794739629293 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863721169/2000000000 : ℝ), (4495973451/10000000000 : ℝ), (4147759143/10000000000 : ℝ)] ![(8326017963373/25000000000000 : ℝ), (35106448873519/100000000000000 : ℝ), (15794739629293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863721169/2000000000 : ℝ)|^4333 ≤ (8326017963373/25000000000000 : ℝ)^3309
        have hw : |(863721169/2000000000 : ℝ)|=(863721169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495973451/10000000000 : ℝ)|^4333 ≤ (35106448873519/100000000000000 : ℝ)^3309
        have hw : |(4495973451/10000000000 : ℝ)|=(4495973451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147759143/10000000000 : ℝ)|^4333 ≤ (15794739629293/50000000000000 : ℝ)^3309
        have hw : |(4147759143/10000000000 : ℝ)|=(4147759143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1373_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11221/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (589/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7363/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (561/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7363/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (561/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7363/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (561/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7363/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (561/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7363/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (561/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7363/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (561/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (561/5000 : ℝ) ^ (1083/256 : ℝ) ≤ (1914496005662633/20000000000000000000 : ℝ) := by
    have hpowers : (561/5000 : ℝ)^1083 ≤ (1914496005662633/20000000000000000000 : ℝ)^256 := by
      have hnat : (561 : ℕ)^1083*20000000000000000000^256 ≤ 1914496005662633^256*5000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 5000 1914496005662633 20000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/5000 : ℝ)) (X := (1914496005662633/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7363/50000 : ℝ) ^ (1083/256 : ℝ) ≤ (30241875936418739/100000000000000000000 : ℝ) := by
    have hpowers : (7363/50000 : ℝ)^1083 ≤ (30241875936418739/100000000000000000000 : ℝ)^256 := by
      have hnat : (7363 : ℕ)^1083*100000000000000000000^256 ≤ 30241875936418739^256*50000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7363 50000 30241875936418739 100000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7363/50000 : ℝ)) (X := (30241875936418739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001914496005662633/10000000000000000000 : ℝ) ≤ (2500113129075641/2500000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (10001914496005662633/10000000000000000000 : ℝ)^256 ≤ (2500113129075641/2500000000000000 : ℝ)^1083 := by
      have hnat : (10001914496005662633 : ℕ)^256*2500000000000000^1083 ≤ 2500113129075641^1083*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001914496005662633 10000000000000000000 2500113129075641 2500000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500113129075641/2500000000000000 : ℝ)) (X := (10001914496005662633/10000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (195390262413993617/195312500000000000 : ℝ) ≤ (1000094099040437/1000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (195390262413993617/195312500000000000 : ℝ)^256 ≤ (1000094099040437/1000000000000000 : ℝ)^1083 := by
      have hnat : (195390262413993617 : ℕ)^256*1000000000000000^1083 ≤ 1000094099040437^1083*195312500000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195390262413993617 195312500000000000 1000094099040437 1000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000094099040437/1000000000000000 : ℝ)) (X := (195390262413993617/195312500000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030241875936418739/50000000000000000000 : ℝ) ≤ (156272335382909/156250000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (50030241875936418739/50000000000000000000 : ℝ)^256 ≤ (156272335382909/156250000000000 : ℝ)^1083 := by
      have hnat : (50030241875936418739 : ℕ)^256*156250000000000^1083 ≤ 156272335382909^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030241875936418739 50000000000000000000 156272335382909 156250000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156272335382909/156250000000000 : ℝ)) (X := (50030241875936418739/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1914496005662633/20000000000000000000 : ℝ) ≤ ((4381328145414032843/4382500000000000000 : ℝ)+2*(244237050903/175300000000000 : ℝ)*(561/5000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (4381328145414032843/4382500000000000000 : ℝ)+2*(244237050903/175300000000000 : ℝ)*(561/5000 : ℝ)=(2500113129075641/2500000000000000 : ℝ) by norm_num, show 1+2*(1914496005662633/20000000000000000000 : ℝ)=(10001914496005662633/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30241875936418739/100000000000000000000 : ℝ)+(1914496005662633/20000000000000000000 : ℝ) ≤ ((4381328145414032843/4382500000000000000 : ℝ)+(244237050903/175300000000000 : ℝ)*((7363/50000 : ℝ)+(561/5000 : ℝ)))^(1083/256 : ℝ) := by
    rw [show (4381328145414032843/4382500000000000000 : ℝ)+(244237050903/175300000000000 : ℝ)*((7363/50000 : ℝ)+(561/5000 : ℝ))=(1000094099040437/1000000000000000 : ℝ) by norm_num, show 1+(30241875936418739/100000000000000000000 : ℝ)+(1914496005662633/20000000000000000000 : ℝ)=(195390262413993617/195312500000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30241875936418739/100000000000000000000 : ℝ) ≤ ((4381328145414032843/4382500000000000000 : ℝ)+2*(244237050903/175300000000000 : ℝ)*(7363/50000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (4381328145414032843/4382500000000000000 : ℝ)+2*(244237050903/175300000000000 : ℝ)*(7363/50000 : ℝ)=(156272335382909/156250000000000 : ℝ) by norm_num, show 1+2*(30241875936418739/100000000000000000000 : ℝ)=(50030241875936418739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4381328145414032843/4382500000000000000 : ℝ)*(X 1 0+X 2 0)+(244237050903/175300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (4381328145414032843/4382500000000000000 : ℝ)) (alpha := (244237050903/175300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4381328145414032843/4382500000000000000 : ℝ)*(X 0 1+X 2 1)+(244237050903/175300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (4381328145414032843/4382500000000000000 : ℝ)) (alpha := (244237050903/175300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4381328145414032843/4382500000000000000 : ℝ)*(X 0 2+X 1 2)+(244237050903/175300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (4381328145414032843/4382500000000000000 : ℝ)) (alpha := (244237050903/175300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-504373253/2500000000 : ℝ)*X 0 0+(2705533711/5000000000 : ℝ)*X 0 1+(5245549411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348430859/10000000000 : ℝ)*X 1 0+(-410508/1953125 : ℝ)*X 1 1+(5245549449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069686177/2000000000 : ℝ)*X 2 0+(1049109887/2000000000 : ℝ)*X 2 1+(-2101800943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318580783/10000000000 : ℝ)*X 0 0+(259155899/625000000 : ℝ)*X 0 1+(4497231687/10000000000 : ℝ)*X 0 2+(4318580783/10000000000 : ℝ)*X 1 0+(259155899/625000000 : ℝ)*X 1 1+(4497231687/10000000000 : ℝ)*X 1 2+(4318580783/10000000000 : ℝ)*X 2 0+(259155899/625000000 : ℝ)*X 2 1+(4497231687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-201750497/1000000000 : ℝ)*X 0 0+(524614303/1000000000 : ℝ)*X 0 1+(5410470651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305649223/10000000000 : ℝ)*X 1 0+(-484219927/2500000000 : ℝ)*X 1 1+(1082094047/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663206123/1250000000 : ℝ)*X 2 0+(676308803/1250000000 : ℝ)*X 2 1+(-968439887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863721169/2000000000 : ℝ)*X 0 0+(4495973451/10000000000 : ℝ)*X 0 1+(4147759143/10000000000 : ℝ)*X 0 2+(863721169/2000000000 : ℝ)*X 1 0+(4495973451/10000000000 : ℝ)*X 1 1+(4147759143/10000000000 : ℝ)*X 1 2+(863721169/2000000000 : ℝ)*X 2 0+(4495973451/10000000000 : ℝ)*X 2 1+(4147759143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30265970610336207164438661/6847656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (96846051/12500000000000 : ℝ)*(base19) + (48322677/6250000000000 : ℝ)*(base23) + (16567079/100000000000000 : ℝ)*(lower2) + (99730799/100000000000000 : ℝ)*(upper3) + (51372603/50000000000000 : ℝ)*(upper5) + (555801613440343/12500000000000 : ℝ)*(major0) + (555801613440343/12500000000000 : ℝ)*(major1) + (555801613440343/12500000000000 : ℝ)*(major2) + (6041655388289701/100000000000000 : ℝ)*(sp0) + (302083614696119/5000000000000 : ℝ)*(sp1) + (1510418073881989/25000000000000 : ℝ)*(sp2) + (1425572263315097/50000000000000 : ℝ)*(sp3) + (276256267/1562500000000 : ℝ)*(sp4) + (8072394423/100000000000000 : ℝ)*(sp7) + (356394074878077/12500000000000 : ℝ)*(f.failure) + (1510418267172697/25000000000000 : ℝ)*(f.sum) + (3074391730607/8765000000000000000000000000 : ℝ)*base65 + (44496882172433601/54781250000000000000000000000000 : ℝ)*base68 + (304339110908527351/54781250000000000000000000000000 : ℝ)*base70 + (412197234252996101/54781250000000000000000000000000 : ℝ)*base72 + (17202503242047/8765000000000000000000000000 : ℝ)*base73 + (5638002765183601/54781250000000000000000000000000 : ℝ)*base76 + (516752543937996101/54781250000000000000000000000000 : ℝ)*base78 + (731881213180878899/54781250000000000000000000000000 : ℝ)*base79 + (34158159842303/8765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7368407/625000000000000000000 : ℝ)*base90 + (7368407/625000000000000000000 : ℝ)*base92 + (7368407/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9092476873048006987311/8765000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1149647029/100000000000000 : ℝ)*(base19) + (250420733/25000000000000 : ℝ)*(base23) + (215464233/100000000000000 : ℝ)*(lower1) + (42960027/50000000000000 : ℝ)*(upper2) + (131333051/100000000000000 : ℝ)*(upper5) + (1119647300381641/25000000000000 : ℝ)*(major0) + (1119647300381641/25000000000000 : ℝ)*(major1) + (1119647300381641/25000000000000 : ℝ)*(major2) + (429413807/50000000000000 : ℝ)*(sp0) + (443735541/10000000000000 : ℝ)*(sp1) + (1217078531154449/20000000000000 : ℝ)*(sp4) + (304269396379871/5000000000000 : ℝ)*(sp5) + (6085392512916927/100000000000000 : ℝ)*(sp6) + (1435892426937267/50000000000000 : ℝ)*(sp7) + (1435892426937267/50000000000000 : ℝ)*(f.failure) + (6085393514599859/100000000000000 : ℝ)*(f.sum) + (3759967508861/1095625000000000000000000000 : ℝ)*base66 + (424961973736560363/109562500000000000000000000000000 : ℝ)*base67 + (959660837423622863/109562500000000000000000000000000 : ℝ)*base69 + (484106880473689637/109562500000000000000000000000000 : ℝ)*base72 + (17553704270841/4382500000000000000000000000 : ℝ)*base73 + (977810310262810363/109562500000000000000000000000000 : ℝ)*base75 + (674696362189564637/109562500000000000000000000000000 : ℝ)*base78 + (221333363967814637/109562500000000000000000000000000 : ℝ)*base80 + (2105289767667/2191250000000000000000000000 : ℝ)*base82 + (7152697/2500000000000000000000 : ℝ)*base90 + (7152697/2500000000000000000000 : ℝ)*base92 + (7152697/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1373_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1373_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1373_box_0 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1852665401/10000000000 : ℝ)*x 0 + (336789771/625000000 : ℝ)*x 1 + (5388636037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1852665401/10000000000 : ℝ)^4333 ≤ (1374422182009/12500000000000 : ℝ)^3309 := by
    have hnat : (1852665401 : ℕ)^4333*12500000000000^3309 ≤ 1374422182009^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852665401 10000000000 1374422182009 12500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336789771/625000000 : ℝ)^4333 ≤ (8900462576701/20000000000000 : ℝ)^3309 := by
    have hnat : (336789771 : ℕ)^4333*20000000000000^3309 ≤ 8900462576701^3309*625000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336789771 625000000 8900462576701 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388636037/10000000000 : ℝ)^4333 ≤ (890046193001/2000000000000 : ℝ)^3309 := by
    have hnat : (5388636037 : ℕ)^4333*2000000000000^3309 ≤ 890046193001^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388636037 10000000000 890046193001 2000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1852665401/10000000000 : ℝ), (336789771/625000000 : ℝ), (5388636037/10000000000 : ℝ)] ![(1374422182009/12500000000000 : ℝ), (8900462576701/20000000000000 : ℝ), (890046193001/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1852665401/10000000000 : ℝ)|^4333 ≤ (1374422182009/12500000000000 : ℝ)^3309
        have hw : |(-1852665401/10000000000 : ℝ)|=(1852665401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336789771/625000000 : ℝ)|^4333 ≤ (8900462576701/20000000000000 : ℝ)^3309
        have hw : |(336789771/625000000 : ℝ)|=(336789771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388636037/10000000000 : ℝ)|^4333 ≤ (890046193001/2000000000000 : ℝ)^3309
        have hw : |(5388636037/10000000000 : ℝ)|=(5388636037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_1 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642776599/5000000000 : ℝ)*x 0 + (-1994039993/10000000000 : ℝ)*x 1 + (2694318279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642776599/5000000000 : ℝ)^4333 ≤ (1355964447731/3125000000000 : ℝ)^3309 := by
    have hnat : (2642776599 : ℕ)^4333*3125000000000^3309 ≤ 1355964447731^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642776599 5000000000 1355964447731 3125000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1994039993/10000000000 : ℝ)^4333 ≤ (12106822370789/100000000000000 : ℝ)^3309 := by
    have hnat : (1994039993 : ℕ)^4333*100000000000000^3309 ≤ 12106822370789^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994039993 10000000000 12106822370789 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694318279/5000000000 : ℝ)^4333 ≤ (5562789410533/12500000000000 : ℝ)^3309 := by
    have hnat : (2694318279 : ℕ)^4333*12500000000000^3309 ≤ 5562789410533^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694318279 5000000000 5562789410533 12500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642776599/5000000000 : ℝ), (-1994039993/10000000000 : ℝ), (2694318279/5000000000 : ℝ)] ![(1355964447731/3125000000000 : ℝ), (12106822370789/100000000000000 : ℝ), (5562789410533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642776599/5000000000 : ℝ)|^4333 ≤ (1355964447731/3125000000000 : ℝ)^3309
        have hw : |(2642776599/5000000000 : ℝ)|=(2642776599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1994039993/10000000000 : ℝ)|^4333 ≤ (12106822370789/100000000000000 : ℝ)^3309
        have hw : |(-1994039993/10000000000 : ℝ)|=(1994039993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694318279/5000000000 : ℝ)|^4333 ≤ (5562789410533/12500000000000 : ℝ)^3309
        have hw : |(2694318279/5000000000 : ℝ)|=(2694318279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_2 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660694049/1250000000 : ℝ)*x 0 + (5388636941/10000000000 : ℝ)*x 1 + (-1994040563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660694049/1250000000 : ℝ)^4333 ≤ (21695426831533/50000000000000 : ℝ)^3309 := by
    have hnat : (660694049 : ℕ)^4333*50000000000000^3309 ≤ 21695426831533^3309*1250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660694049 1250000000 21695426831533 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388636941/10000000000 : ℝ)^4333 ≤ (8900463885223/20000000000000 : ℝ)^3309 := by
    have hnat : (5388636941 : ℕ)^4333*20000000000000^3309 ≤ 8900463885223^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388636941 10000000000 8900463885223 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1994040563/10000000000 : ℝ)^4333 ≤ (12106826902509/100000000000000 : ℝ)^3309 := by
    have hnat : (1994040563 : ℕ)^4333*100000000000000^3309 ≤ 12106826902509^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994040563 10000000000 12106826902509 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660694049/1250000000 : ℝ), (5388636941/10000000000 : ℝ), (-1994040563/10000000000 : ℝ)] ![(21695426831533/50000000000000 : ℝ), (8900463885223/20000000000000 : ℝ), (12106826902509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660694049/1250000000 : ℝ)|^4333 ≤ (21695426831533/50000000000000 : ℝ)^3309
        have hw : |(660694049/1250000000 : ℝ)|=(660694049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388636941/10000000000 : ℝ)|^4333 ≤ (8900463885223/20000000000000 : ℝ)^3309
        have hw : |(5388636941/10000000000 : ℝ)|=(5388636941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1994040563/10000000000 : ℝ)|^4333 ≤ (12106826902509/100000000000000 : ℝ)^3309
        have hw : |(-1994040563/10000000000 : ℝ)|=(1994040563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_3 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4466056201/10000000000 : ℝ)*x 0 + (3319269/7812500 : ℝ)*x 1 + (1062166319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4466056201/10000000000 : ℝ)^4333 ≤ (34800866228471/100000000000000 : ℝ)^3309 := by
    have hnat : (4466056201 : ℕ)^4333*100000000000000^3309 ≤ 34800866228471^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4466056201 10000000000 34800866228471 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3319269/7812500 : ℝ)^4333 ≤ (32599562077789/100000000000000 : ℝ)^3309 := by
    have hnat : (3319269 : ℕ)^4333*100000000000000^3309 ≤ 32599562077789^3309*7812500^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319269 7812500 32599562077789 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062166319/2500000000 : ℝ)^4333 ≤ (651991433661/2000000000000 : ℝ)^3309 := by
    have hnat : (1062166319 : ℕ)^4333*2000000000000^3309 ≤ 651991433661^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062166319 2500000000 651991433661 2000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4466056201/10000000000 : ℝ), (3319269/7812500 : ℝ), (1062166319/2500000000 : ℝ)] ![(34800866228471/100000000000000 : ℝ), (32599562077789/100000000000000 : ℝ), (651991433661/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4466056201/10000000000 : ℝ)|^4333 ≤ (34800866228471/100000000000000 : ℝ)^3309
        have hw : |(4466056201/10000000000 : ℝ)|=(4466056201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3319269/7812500 : ℝ)|^4333 ≤ (32599562077789/100000000000000 : ℝ)^3309
        have hw : |(3319269/7812500 : ℝ)|=(3319269/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062166319/2500000000 : ℝ)|^4333 ≤ (651991433661/2000000000000 : ℝ)^3309
        have hw : |(1062166319/2500000000 : ℝ)|=(1062166319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_4 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-437013203/2000000000 : ℝ)*x 0 + (5265573199/10000000000 : ℝ)*x 1 + (1316393243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437013203/2000000000 : ℝ)^4333 ≤ (2729517532801/20000000000000 : ℝ)^3309 := by
    have hnat : (437013203 : ℕ)^4333*20000000000000^3309 ≤ 2729517532801^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437013203 2000000000 2729517532801 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265573199/10000000000 : ℝ)^4333 ≤ (8635241475837/20000000000000 : ℝ)^3309 := by
    have hnat : (5265573199 : ℕ)^4333*20000000000000^3309 ≤ 8635241475837^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265573199 10000000000 8635241475837 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316393243/2500000000 : ℝ)^4333 ≤ (21588102470921/50000000000000 : ℝ)^3309 := by
    have hnat : (1316393243 : ℕ)^4333*50000000000000^3309 ≤ 21588102470921^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316393243 2500000000 21588102470921 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437013203/2000000000 : ℝ), (5265573199/10000000000 : ℝ), (1316393243/2500000000 : ℝ)] ![(2729517532801/20000000000000 : ℝ), (8635241475837/20000000000000 : ℝ), (21588102470921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437013203/2000000000 : ℝ)|^4333 ≤ (2729517532801/20000000000000 : ℝ)^3309
        have hw : |(-437013203/2000000000 : ℝ)|=(437013203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265573199/10000000000 : ℝ)|^4333 ≤ (8635241475837/20000000000000 : ℝ)^3309
        have hw : |(5265573199/10000000000 : ℝ)|=(5265573199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316393243/2500000000 : ℝ)|^4333 ≤ (21588102470921/50000000000000 : ℝ)^3309
        have hw : |(1316393243/2500000000 : ℝ)|=(1316393243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_5 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685938601/5000000000 : ℝ)*x 0 + (-2043634631/10000000000 : ℝ)*x 1 + (42124587/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685938601/5000000000 : ℝ)^4333 ≤ (443211630203/1000000000000 : ℝ)^3309 := by
    have hnat : (2685938601 : ℕ)^4333*1000000000000^3309 ≤ 443211630203^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685938601 5000000000 443211630203 1000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2043634631/10000000000 : ℝ)^4333 ≤ (6251313845519/50000000000000 : ℝ)^3309 := by
    have hnat : (2043634631 : ℕ)^4333*50000000000000^3309 ≤ 6251313845519^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043634631 10000000000 6251313845519 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42124587/80000000 : ℝ)^4333 ≤ (43176209268931/100000000000000 : ℝ)^3309 := by
    have hnat : (42124587 : ℕ)^4333*100000000000000^3309 ≤ 43176209268931^3309*80000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42124587 80000000 43176209268931 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685938601/5000000000 : ℝ), (-2043634631/10000000000 : ℝ), (42124587/80000000 : ℝ)] ![(443211630203/1000000000000 : ℝ), (6251313845519/50000000000000 : ℝ), (43176209268931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685938601/5000000000 : ℝ)|^4333 ≤ (443211630203/1000000000000 : ℝ)^3309
        have hw : |(2685938601/5000000000 : ℝ)|=(2685938601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2043634631/10000000000 : ℝ)|^4333 ≤ (6251313845519/50000000000000 : ℝ)^3309
        have hw : |(-2043634631/10000000000 : ℝ)|=(2043634631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42124587/80000000 : ℝ)|^4333 ≤ (43176209268931/100000000000000 : ℝ)^3309
        have hw : |(42124587/80000000 : ℝ)|=(42124587/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_6 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371877753/10000000000 : ℝ)*x 0 + (5265572957/10000000000 : ℝ)*x 1 + (-127727153/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371877753/10000000000 : ℝ)^4333 ≤ (110802922433/250000000000 : ℝ)^3309 := by
    have hnat : (5371877753 : ℕ)^4333*250000000000^3309 ≤ 110802922433^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371877753 10000000000 110802922433 250000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265572957/10000000000 : ℝ)^4333 ≤ (8635240956157/20000000000000 : ℝ)^3309 := by
    have hnat : (5265572957 : ℕ)^4333*20000000000000^3309 ≤ 8635240956157^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265572957 10000000000 8635240956157 20000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127727153/625000000 : ℝ)^4333 ≤ (6251313112507/50000000000000 : ℝ)^3309 := by
    have hnat : (127727153 : ℕ)^4333*50000000000000^3309 ≤ 6251313112507^3309*625000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127727153 625000000 6251313112507 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371877753/10000000000 : ℝ), (5265572957/10000000000 : ℝ), (-127727153/625000000 : ℝ)] ![(110802922433/250000000000 : ℝ), (8635240956157/20000000000000 : ℝ), (6251313112507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371877753/10000000000 : ℝ)|^4333 ≤ (110802922433/250000000000 : ℝ)^3309
        have hw : |(5371877753/10000000000 : ℝ)|=(5371877753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265572957/10000000000 : ℝ)|^4333 ≤ (8635240956157/20000000000000 : ℝ)^3309
        have hw : |(5265572957/10000000000 : ℝ)|=(5265572957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127727153/625000000 : ℝ)|^4333 ≤ (6251313112507/50000000000000 : ℝ)^3309
        have hw : |(-127727153/625000000 : ℝ)|=(127727153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_7 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4170134349/10000000000 : ℝ)*x 0 + (4396573081/10000000000 : ℝ)*x 1 + (4396573207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170134349/10000000000 : ℝ)^4333 ≤ (31812810666759/100000000000000 : ℝ)^3309 := by
    have hnat : (4170134349 : ℕ)^4333*100000000000000^3309 ≤ 31812810666759^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170134349 10000000000 31812810666759 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4396573081/10000000000 : ℝ)^4333 ≤ (34093594021271/100000000000000 : ℝ)^3309 := by
    have hnat : (4396573081 : ℕ)^4333*100000000000000^3309 ≤ 34093594021271^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396573081 10000000000 34093594021271 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4396573207/10000000000 : ℝ)^4333 ≤ (17046797650357/50000000000000 : ℝ)^3309 := by
    have hnat : (4396573207 : ℕ)^4333*50000000000000^3309 ≤ 17046797650357^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396573207 10000000000 17046797650357 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170134349/10000000000 : ℝ), (4396573081/10000000000 : ℝ), (4396573207/10000000000 : ℝ)] ![(31812810666759/100000000000000 : ℝ), (34093594021271/100000000000000 : ℝ), (17046797650357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170134349/10000000000 : ℝ)|^4333 ≤ (31812810666759/100000000000000 : ℝ)^3309
        have hw : |(4170134349/10000000000 : ℝ)|=(4170134349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4396573081/10000000000 : ℝ)|^4333 ≤ (34093594021271/100000000000000 : ℝ)^3309
        have hw : |(4396573081/10000000000 : ℝ)|=(4396573081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4396573207/10000000000 : ℝ)|^4333 ≤ (17046797650357/50000000000000 : ℝ)^3309
        have hw : |(4396573207/10000000000 : ℝ)|=(4396573207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_8 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115183711/10000000000 : ℝ)*x 0 + (2590354331/5000000000 : ℝ)*x 1 + (5402641301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115183711/10000000000 : ℝ)^4333 ≤ (1634861503417/12500000000000 : ℝ)^3309 := by
    have hnat : (2115183711 : ℕ)^4333*12500000000000^3309 ≤ 1634861503417^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115183711 10000000000 1634861503417 12500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590354331/5000000000 : ℝ)^4333 ≤ (42267281283537/100000000000000 : ℝ)^3309 := by
    have hnat : (2590354331 : ℕ)^4333*100000000000000^3309 ≤ 42267281283537^3309*5000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590354331 5000000000 42267281283537 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402641301/10000000000 : ℝ)^4333 ≤ (44653826674461/100000000000000 : ℝ)^3309 := by
    have hnat : (5402641301 : ℕ)^4333*100000000000000^3309 ≤ 44653826674461^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402641301 10000000000 44653826674461 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115183711/10000000000 : ℝ), (2590354331/5000000000 : ℝ), (5402641301/10000000000 : ℝ)] ![(1634861503417/12500000000000 : ℝ), (42267281283537/100000000000000 : ℝ), (44653826674461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115183711/10000000000 : ℝ)|^4333 ≤ (1634861503417/12500000000000 : ℝ)^3309
        have hw : |(-2115183711/10000000000 : ℝ)|=(2115183711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590354331/5000000000 : ℝ)|^4333 ≤ (42267281283537/100000000000000 : ℝ)^3309
        have hw : |(2590354331/5000000000 : ℝ)|=(2590354331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402641301/10000000000 : ℝ)|^4333 ≤ (44653826674461/100000000000000 : ℝ)^3309
        have hw : |(5402641301/10000000000 : ℝ)|=(5402641301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_9 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275724061/10000000000 : ℝ)*x 0 + (-397653333/2000000000 : ℝ)*x 1 + (13506603/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275724061/10000000000 : ℝ)^4333 ≤ (4328523163943/10000000000000 : ℝ)^3309 := by
    have hnat : (5275724061 : ℕ)^4333*10000000000000^3309 ≤ 4328523163943^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275724061 10000000000 4328523163943 10000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397653333/2000000000 : ℝ)^4333 ≤ (6030471379841/50000000000000 : ℝ)^3309 := by
    have hnat : (397653333 : ℕ)^4333*50000000000000^3309 ≤ 6030471379841^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397653333 2000000000 6030471379841 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13506603/25000000 : ℝ)^4333 ≤ (22326912790673/50000000000000 : ℝ)^3309 := by
    have hnat : (13506603 : ℕ)^4333*50000000000000^3309 ≤ 22326912790673^3309*25000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13506603 25000000 22326912790673 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275724061/10000000000 : ℝ), (-397653333/2000000000 : ℝ), (13506603/25000000 : ℝ)] ![(4328523163943/10000000000000 : ℝ), (6030471379841/50000000000000 : ℝ), (22326912790673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275724061/10000000000 : ℝ)|^4333 ≤ (4328523163943/10000000000000 : ℝ)^3309
        have hw : |(5275724061/10000000000 : ℝ)|=(5275724061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397653333/2000000000 : ℝ)|^4333 ≤ (6030471379841/50000000000000 : ℝ)^3309
        have hw : |(-397653333/2000000000 : ℝ)|=(397653333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13506603/25000000 : ℝ)|^4333 ≤ (22326912790673/50000000000000 : ℝ)^3309
        have hw : |(13506603/25000000 : ℝ)|=(13506603/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_10 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275724057/10000000000 : ℝ)*x 0 + (1350660313/2500000000 : ℝ)*x 1 + (-1988266599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275724057/10000000000 : ℝ)^4333 ≤ (5410653949557/12500000000000 : ℝ)^3309 := by
    have hnat : (5275724057 : ℕ)^4333*12500000000000^3309 ≤ 5410653949557^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275724057 10000000000 5410653949557 12500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350660313/2500000000 : ℝ)^4333 ≤ (22326913072069/50000000000000 : ℝ)^3309 := by
    have hnat : (1350660313 : ℕ)^4333*50000000000000^3309 ≤ 22326913072069^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350660313 2500000000 22326913072069 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988266599/10000000000 : ℝ)^4333 ≤ (12060942235427/100000000000000 : ℝ)^3309 := by
    have hnat : (1988266599 : ℕ)^4333*100000000000000^3309 ≤ 12060942235427^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988266599 10000000000 12060942235427 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275724057/10000000000 : ℝ), (1350660313/2500000000 : ℝ), (-1988266599/10000000000 : ℝ)] ![(5410653949557/12500000000000 : ℝ), (22326913072069/50000000000000 : ℝ), (12060942235427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275724057/10000000000 : ℝ)|^4333 ≤ (5410653949557/12500000000000 : ℝ)^3309
        have hw : |(5275724057/10000000000 : ℝ)|=(5275724057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350660313/2500000000 : ℝ)|^4333 ≤ (22326913072069/50000000000000 : ℝ)^3309
        have hw : |(1350660313/2500000000 : ℝ)|=(1350660313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988266599/10000000000 : ℝ)|^4333 ≤ (12060942235427/100000000000000 : ℝ)^3309
        have hw : |(-1988266599/10000000000 : ℝ)|=(1988266599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_11 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1124793627/2500000000 : ℝ)*x 0 + (264488647/625000000 : ℝ)*x 1 + (4231818329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124793627/2500000000 : ℝ)^4333 ≤ (274524864579/781250000000 : ℝ)^3309 := by
    have hnat : (1124793627 : ℕ)^4333*781250000000^3309 ≤ 274524864579^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124793627 2500000000 274524864579 781250000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264488647/625000000 : ℝ)^4333 ≤ (32430408778391/100000000000000 : ℝ)^3309 := by
    have hnat : (264488647 : ℕ)^4333*100000000000000^3309 ≤ 32430408778391^3309*625000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264488647 625000000 32430408778391 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231818329/10000000000 : ℝ)^4333 ≤ (32430408547587/100000000000000 : ℝ)^3309 := by
    have hnat : (4231818329 : ℕ)^4333*100000000000000^3309 ≤ 32430408547587^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231818329 10000000000 32430408547587 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124793627/2500000000 : ℝ), (264488647/625000000 : ℝ), (4231818329/10000000000 : ℝ)] ![(274524864579/781250000000 : ℝ), (32430408778391/100000000000000 : ℝ), (32430408547587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124793627/2500000000 : ℝ)|^4333 ≤ (274524864579/781250000000 : ℝ)^3309
        have hw : |(1124793627/2500000000 : ℝ)|=(1124793627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264488647/625000000 : ℝ)|^4333 ≤ (32430408778391/100000000000000 : ℝ)^3309
        have hw : |(264488647/625000000 : ℝ)|=(264488647/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231818329/10000000000 : ℝ)|^4333 ≤ (32430408547587/100000000000000 : ℝ)^3309
        have hw : |(4231818329/10000000000 : ℝ)|=(4231818329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_12 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1922825739/10000000000 : ℝ)*x 0 + (5471363407/10000000000 : ℝ)*x 1 + (5254480657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922825739/10000000000 : ℝ)^4333 ≤ (2885949085649/25000000000000 : ℝ)^3309 := by
    have hnat : (1922825739 : ℕ)^4333*25000000000000^3309 ≤ 2885949085649^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922825739 10000000000 2885949085649 25000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471363407/10000000000 : ℝ)^4333 ≤ (22699530090159/50000000000000 : ℝ)^3309 := by
    have hnat : (5471363407 : ℕ)^4333*50000000000000^3309 ≤ 22699530090159^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471363407 10000000000 22699530090159 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254480657/10000000000 : ℝ)^4333 ≤ (84095983313/195312500000 : ℝ)^3309 := by
    have hnat : (5254480657 : ℕ)^4333*195312500000^3309 ≤ 84095983313^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254480657 10000000000 84095983313 195312500000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1922825739/10000000000 : ℝ), (5471363407/10000000000 : ℝ), (5254480657/10000000000 : ℝ)] ![(2885949085649/25000000000000 : ℝ), (22699530090159/50000000000000 : ℝ), (84095983313/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1922825739/10000000000 : ℝ)|^4333 ≤ (2885949085649/25000000000000 : ℝ)^3309
        have hw : |(-1922825739/10000000000 : ℝ)|=(1922825739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471363407/10000000000 : ℝ)|^4333 ≤ (22699530090159/50000000000000 : ℝ)^3309
        have hw : |(5471363407/10000000000 : ℝ)|=(5471363407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254480657/10000000000 : ℝ)|^4333 ≤ (84095983313/195312500000 : ℝ)^3309
        have hw : |(5254480657/10000000000 : ℝ)|=(5254480657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_13 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215186257/400000000 : ℝ)*x 0 + (-409600491/2000000000 : ℝ)*x 1 + (5254480589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215186257/400000000 : ℝ)^4333 ≤ (44405227104041/100000000000000 : ℝ)^3309 := by
    have hnat : (215186257 : ℕ)^4333*100000000000000^3309 ≤ 44405227104041^3309*400000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215186257 400000000 44405227104041 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409600491/2000000000 : ℝ)^4333 ≤ (6268815077799/50000000000000 : ℝ)^3309 := by
    have hnat : (409600491 : ℕ)^4333*50000000000000^3309 ≤ 6268815077799^3309*2000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409600491 2000000000 6268815077799 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254480589/10000000000 : ℝ)^4333 ≤ (43057142726603/100000000000000 : ℝ)^3309 := by
    have hnat : (5254480589 : ℕ)^4333*100000000000000^3309 ≤ 43057142726603^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254480589 10000000000 43057142726603 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215186257/400000000 : ℝ), (-409600491/2000000000 : ℝ), (5254480589/10000000000 : ℝ)] ![(44405227104041/100000000000000 : ℝ), (6268815077799/50000000000000 : ℝ), (43057142726603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215186257/400000000 : ℝ)|^4333 ≤ (44405227104041/100000000000000 : ℝ)^3309
        have hw : |(215186257/400000000 : ℝ)|=(215186257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409600491/2000000000 : ℝ)|^4333 ≤ (6268815077799/50000000000000 : ℝ)^3309
        have hw : |(-409600491/2000000000 : ℝ)|=(409600491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254480589/10000000000 : ℝ)|^4333 ≤ (43057142726603/100000000000000 : ℝ)^3309
        have hw : |(5254480589/10000000000 : ℝ)|=(5254480589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_14 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672457037/1250000000 : ℝ)*x 0 + (105089623/200000000 : ℝ)*x 1 + (-2048001879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672457037/1250000000 : ℝ)^4333 ≤ (1776209028389/4000000000000 : ℝ)^3309 := by
    have hnat : (672457037 : ℕ)^4333*4000000000000^3309 ≤ 1776209028389^3309*1250000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672457037 1250000000 1776209028389 4000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105089623/200000000 : ℝ)^4333 ≤ (43057148746239/100000000000000 : ℝ)^3309 := by
    have hnat : (105089623 : ℕ)^4333*100000000000000^3309 ≤ 43057148746239^3309*200000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105089623 200000000 43057148746239 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048001879/10000000000 : ℝ)^4333 ≤ (6268812769089/50000000000000 : ℝ)^3309 := by
    have hnat : (2048001879 : ℕ)^4333*50000000000000^3309 ≤ 6268812769089^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048001879 10000000000 6268812769089 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672457037/1250000000 : ℝ), (105089623/200000000 : ℝ), (-2048001879/10000000000 : ℝ)] ![(1776209028389/4000000000000 : ℝ), (43057148746239/100000000000000 : ℝ), (6268812769089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672457037/1250000000 : ℝ)|^4333 ≤ (1776209028389/4000000000000 : ℝ)^3309
        have hw : |(672457037/1250000000 : ℝ)|=(672457037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105089623/200000000 : ℝ)|^4333 ≤ (43057148746239/100000000000000 : ℝ)^3309
        have hw : |(105089623/200000000 : ℝ)|=(105089623/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048001879/10000000000 : ℝ)|^4333 ≤ (6268812769089/50000000000000 : ℝ)^3309
        have hw : |(-2048001879/10000000000 : ℝ)|=(2048001879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1373_box_15 (p : ℝ) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035753097/2500000000 : ℝ)*x 0 + (220494727/500000000 : ℝ)*x 1 + (4409894141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035753097/2500000000 : ℝ)^4333 ≤ (3942768599539/12500000000000 : ℝ)^3309 := by
    have hnat : (1035753097 : ℕ)^4333*12500000000000^3309 ≤ 3942768599539^3309*2500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035753097 2500000000 3942768599539 12500000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220494727/500000000 : ℝ)^4333 ≤ (34228927617283/100000000000000 : ℝ)^3309 := by
    have hnat : (220494727 : ℕ)^4333*100000000000000^3309 ≤ 34228927617283^3309*500000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220494727 500000000 34228927617283 100000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4409894141/10000000000 : ℝ)^4333 ≤ (17114461780959/50000000000000 : ℝ)^3309 := by
    have hnat : (4409894141 : ℕ)^4333*50000000000000^3309 ≤ 17114461780959^3309*10000000000^4333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409894141 10000000000 17114461780959 50000000000000 4333 3309 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4333/1024 : ℝ)) 4333 3309 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035753097/2500000000 : ℝ), (220494727/500000000 : ℝ), (4409894141/10000000000 : ℝ)] ![(3942768599539/12500000000000 : ℝ), (34228927617283/100000000000000 : ℝ), (17114461780959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035753097/2500000000 : ℝ)|^4333 ≤ (3942768599539/12500000000000 : ℝ)^3309
        have hw : |(1035753097/2500000000 : ℝ)|=(1035753097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220494727/500000000 : ℝ)|^4333 ≤ (34228927617283/100000000000000 : ℝ)^3309
        have hw : |(220494727/500000000 : ℝ)|=(220494727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4409894141/10000000000 : ℝ)|^4333 ≤ (17114461780959/50000000000000 : ℝ)^3309
        have hw : |(4409894141/10000000000 : ℝ)|=(4409894141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1373_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62869/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29501/50000 : ℝ) ∧ (40067/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10559/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11221/100000 : ℝ) ^ (1083/256 : ℝ) ≤ (9576089824020197/100000000000000000000 : ℝ) := by
    have hpowers : (11221/100000 : ℝ)^1083 ≤ (9576089824020197/100000000000000000000 : ℝ)^256 := by
      have hnat : (11221 : ℕ)^1083*100000000000000000000^256 ≤ 9576089824020197^256*100000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11221 100000 9576089824020197 100000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11221/100000 : ℝ)) (X := (9576089824020197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hpowhi : (589/4000 : ℝ) ^ (1083/256 : ℝ) ≤ (15116594518566513/50000000000000000000 : ℝ) := by
    have hpowers : (589/4000 : ℝ)^1083 ≤ (15116594518566513/50000000000000000000 : ℝ)^256 := by
      have hnat : (589 : ℕ)^1083*50000000000000000000^256 ≤ 15116594518566513^256*4000^1083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 4000 15116594518566513 50000000000000000000 1083 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/4000 : ℝ)) (X := (15116594518566513/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009576089824020197/50000000000000000000 : ℝ) ≤ (10000452686934623/10000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (50009576089824020197/50000000000000000000 : ℝ)^256 ≤ (10000452686934623/10000000000000000 : ℝ)^1083 := by
      have hnat : (50009576089824020197 : ℕ)^256*10000000000000000^1083 ≤ 10000452686934623^1083*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009576089824020197 50000000000000000000 10000452686934623 10000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000452686934623/10000000000000000 : ℝ)) (X := (50009576089824020197/50000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039809278861153223/100000000000000000000 : ℝ) ≤ (2500235217607013/2500000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (100039809278861153223/100000000000000000000 : ℝ)^256 ≤ (2500235217607013/2500000000000000 : ℝ)^1083 := by
      have hnat : (100039809278861153223 : ℕ)^256*2500000000000000^1083 ≤ 2500235217607013^1083*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039809278861153223 100000000000000000000 2500235217607013 2500000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500235217607013/2500000000000000 : ℝ)) (X := (100039809278861153223/100000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015116594518566513/25000000000000000000 : ℝ) ≤ (10001429053921481/10000000000000000 : ℝ) ^ (1083/256 : ℝ) := by
    have hpowers : (25015116594518566513/25000000000000000000 : ℝ)^256 ≤ (10001429053921481/10000000000000000 : ℝ)^1083 := by
      have hnat : (25015116594518566513 : ℕ)^256*10000000000000000^1083 ≤ 10001429053921481^1083*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015116594518566513 25000000000000000000 10001429053921481 10000000000000000 256 1083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001429053921481/10000000000000000 : ℝ)) (X := (25015116594518566513/25000000000000000000 : ℝ)) (by norm_num) 1083 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9576089824020197/100000000000000000000 : ℝ) ≤ ((5838438400176564229/5840000000000000000 : ℝ)+2*(162727831143/116800000000000 : ℝ)*(11221/100000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (5838438400176564229/5840000000000000000 : ℝ)+2*(162727831143/116800000000000 : ℝ)*(11221/100000 : ℝ)=(10000452686934623/10000000000000000 : ℝ) by norm_num, show 1+2*(9576089824020197/100000000000000000000 : ℝ)=(50009576089824020197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15116594518566513/50000000000000000000 : ℝ)+(9576089824020197/100000000000000000000 : ℝ) ≤ ((5838438400176564229/5840000000000000000 : ℝ)+(162727831143/116800000000000 : ℝ)*((589/4000 : ℝ)+(11221/100000 : ℝ)))^(1083/256 : ℝ) := by
    rw [show (5838438400176564229/5840000000000000000 : ℝ)+(162727831143/116800000000000 : ℝ)*((589/4000 : ℝ)+(11221/100000 : ℝ))=(2500235217607013/2500000000000000 : ℝ) by norm_num, show 1+(15116594518566513/50000000000000000000 : ℝ)+(9576089824020197/100000000000000000000 : ℝ)=(100039809278861153223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15116594518566513/50000000000000000000 : ℝ) ≤ ((5838438400176564229/5840000000000000000 : ℝ)+2*(162727831143/116800000000000 : ℝ)*(589/4000 : ℝ))^(1083/256 : ℝ) := by
    rw [show (5838438400176564229/5840000000000000000 : ℝ)+2*(162727831143/116800000000000 : ℝ)*(589/4000 : ℝ)=(10001429053921481/10000000000000000 : ℝ) by norm_num, show 1+2*(15116594518566513/50000000000000000000 : ℝ)=(25015116594518566513/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5838438400176564229/5840000000000000000 : ℝ)*(X 1 0+X 2 0)+(162727831143/116800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (5838438400176564229/5840000000000000000 : ℝ)) (alpha := (162727831143/116800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5838438400176564229/5840000000000000000 : ℝ)*(X 0 1+X 2 1)+(162727831143/116800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (5838438400176564229/5840000000000000000 : ℝ)) (alpha := (162727831143/116800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5838438400176564229/5840000000000000000 : ℝ)*(X 0 2+X 1 2)+(162727831143/116800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1083/256 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (5838438400176564229/5840000000000000000 : ℝ)) (alpha := (162727831143/116800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1852665401/10000000000 : ℝ)*X 0 0+(336789771/625000000 : ℝ)*X 0 1+(5388636037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642776599/5000000000 : ℝ)*X 1 0+(-1994039993/10000000000 : ℝ)*X 1 1+(2694318279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660694049/1250000000 : ℝ)*X 2 0+(5388636941/10000000000 : ℝ)*X 2 1+(-1994040563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4466056201/10000000000 : ℝ)*X 0 0+(3319269/7812500 : ℝ)*X 0 1+(1062166319/2500000000 : ℝ)*X 0 2+(4466056201/10000000000 : ℝ)*X 1 0+(3319269/7812500 : ℝ)*X 1 1+(1062166319/2500000000 : ℝ)*X 1 2+(4466056201/10000000000 : ℝ)*X 2 0+(3319269/7812500 : ℝ)*X 2 1+(1062166319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-437013203/2000000000 : ℝ)*X 0 0+(5265573199/10000000000 : ℝ)*X 0 1+(1316393243/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685938601/5000000000 : ℝ)*X 1 0+(-2043634631/10000000000 : ℝ)*X 1 1+(42124587/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5371877753/10000000000 : ℝ)*X 2 0+(5265572957/10000000000 : ℝ)*X 2 1+(-127727153/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4170134349/10000000000 : ℝ)*X 0 0+(4396573081/10000000000 : ℝ)*X 0 1+(4396573207/10000000000 : ℝ)*X 0 2+(4170134349/10000000000 : ℝ)*X 1 0+(4396573081/10000000000 : ℝ)*X 1 1+(4396573207/10000000000 : ℝ)*X 1 2+(4170134349/10000000000 : ℝ)*X 2 0+(4396573081/10000000000 : ℝ)*X 2 1+(4396573207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2115183711/10000000000 : ℝ)*X 0 0+(2590354331/5000000000 : ℝ)*X 0 1+(5402641301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275724061/10000000000 : ℝ)*X 1 0+(-397653333/2000000000 : ℝ)*X 1 1+(13506603/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275724057/10000000000 : ℝ)*X 2 0+(1350660313/2500000000 : ℝ)*X 2 1+(-1988266599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1124793627/2500000000 : ℝ)*X 0 0+(264488647/625000000 : ℝ)*X 0 1+(4231818329/10000000000 : ℝ)*X 0 2+(1124793627/2500000000 : ℝ)*X 1 0+(264488647/625000000 : ℝ)*X 1 1+(4231818329/10000000000 : ℝ)*X 1 2+(1124793627/2500000000 : ℝ)*X 2 0+(264488647/625000000 : ℝ)*X 2 1+(4231818329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1922825739/10000000000 : ℝ)*X 0 0+(5471363407/10000000000 : ℝ)*X 0 1+(5254480657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((215186257/400000000 : ℝ)*X 1 0+(-409600491/2000000000 : ℝ)*X 1 1+(5254480589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672457037/1250000000 : ℝ)*X 2 0+(105089623/200000000 : ℝ)*X 2 1+(-2048001879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1035753097/2500000000 : ℝ)*X 0 0+(220494727/500000000 : ℝ)*X 0 1+(4409894141/10000000000 : ℝ)*X 0 2+(1035753097/2500000000 : ℝ)*X 1 0+(220494727/500000000 : ℝ)*X 1 1+(4409894141/10000000000 : ℝ)*X 1 2+(1035753097/2500000000 : ℝ)*X 2 0+(220494727/500000000 : ℝ)*X 2 1+(4409894141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1373_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62869/100000 : ℝ) ≤ (-45892351512615397355044848152367/73000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582297/25000000000000 : ℝ)*(upper0) + (380567/12500000000000 : ℝ)*(upper1) + (115239211/100000000000000 : ℝ)*(upper4) + (160034647/100000000000000 : ℝ)*(upper5) + (1477658115195641/50000000000000 : ℝ)*(major0) + (1477658115195641/50000000000000 : ℝ)*(major1) + (1477658115195641/50000000000000 : ℝ)*(major2) + (12415294631/100000000000000 : ℝ)*(sp2) + (1826198077/25000000000000 : ℝ)*(sp3) + (1009138036785233/25000000000000 : ℝ)*(sp4) + (403656423732081/10000000000000 : ℝ)*(sp5) + (4036551822026179/100000000000000 : ℝ)*(sp6) + (236877041289879/12500000000000 : ℝ)*(sp7) + (6045089939/50000000000000 : ℝ)*(sp8) + (94751181755567/5000000000000 : ℝ)*(f.failure) + (403656423732081/10000000000000 : ℝ)*(f.sum) + (10286923759297/2920000000000000000000000000 : ℝ)*base66 + (997906639968475789/292000000000000000000000000000000 : ℝ)*base67 + (171521519767524211/292000000000000000000000000000000 : ℝ)*base70 + (1438741130688475789/292000000000000000000000000000000 : ℝ)*base71 + (2641907085023/2920000000000000000000000000 : ℝ)*base73 + (1448084930376475789/292000000000000000000000000000000 : ℝ)*base75 + (3242912911140475789/292000000000000000000000000000000 : ℝ)*base77 + (417930291928475789/292000000000000000000000000000000 : ℝ)*base79 + (883237381623/2920000000000000000000000000 : ℝ)*base81 + (3477997/250000000000000000000 : ℝ)*base90 + (3477997/250000000000000000000 : ℝ)*base92 + (3477997/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29501/50000 : ℝ) ≤ (1722926381656572966406470609/2920000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13199667/50000000000000 : ℝ)*(lower0) + (8515443/20000000000000 : ℝ)*(lower1) + (370899151/100000000000000 : ℝ)*(lower4) + (321933/800000000000 : ℝ)*(lower5) + (1512523402920859/50000000000000 : ℝ)*(major0) + (1512523402920859/50000000000000 : ℝ)*(major1) + (1512523402920859/50000000000000 : ℝ)*(major2) + (40906819624303/1000000000000 : ℝ)*(sp0) + (2045333741282703/50000000000000 : ℝ)*(sp1) + (2045336127170739/50000000000000 : ℝ)*(sp2) + (24246708082527/1250000000000 : ℝ)*(sp3) + (21373136219/100000000000000 : ℝ)*(sp5) + (8300680073/50000000000000 : ℝ)*(sp6) + (275730853/4000000000000 : ℝ)*(sp12) + (24246708082527/1250000000000 : ℝ)*(f.failure) + (511336106962703/12500000000000 : ℝ)*(f.sum) + (16181880231637/2920000000000000000000000000 : ℝ)*base65 + (220617148890797289/292000000000000000000000000000000 : ℝ)*base68 + (416975909810797289/292000000000000000000000000000000 : ℝ)*base70 + (102561001897202711/292000000000000000000000000000000 : ℝ)*base71 + (96620465861077/2920000000000000000000000000 : ℝ)*base73 + (1604335523826797289/292000000000000000000000000000000 : ℝ)*base76 + (613006293001202711/292000000000000000000000000000000 : ℝ)*base77 + (772263021169202711/292000000000000000000000000000000 : ℝ)*base79 + (9017734231123/2920000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (413357/62500000000000000000 : ℝ)*base90 + (413357/62500000000000000000 : ℝ)*base92 + (413357/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40067/50000 : ℝ) ≤ (58499597766352586740840540305339/73000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2578703/50000000000000 : ℝ)*(upper0) + (4163079/100000000000000 : ℝ)*(lower3) + (6145143/25000000000000 : ℝ)*(upper4) + (833947654819399/25000000000000 : ℝ)*(major0) + (833947654819399/25000000000000 : ℝ)*(major1) + (833947654819399/25000000000000 : ℝ)*(major2) + (3130456071/100000000000000 : ℝ)*(sp1) + (7493611679/25000000000000 : ℝ)*(sp2) + (387854039/3125000000000 : ℝ)*(sp3) + (667263643/20000000000000 : ℝ)*(sp4) + (2252936152583051/50000000000000 : ℝ)*(sp8) + (4505872511028247/100000000000000 : ℝ)*(sp9) + (4505845667037601/100000000000000 : ℝ)*(sp10) + (85559241625713/4000000000000 : ℝ)*(sp11) + (267374181496509/12500000000000 : ℝ)*(f.failure) + (4505875641484317/100000000000000 : ℝ)*(f.sum) + (7933655790403/1460000000000000000000000000 : ℝ)*base66 + (617898873602471629/146000000000000000000000000000000 : ℝ)*base68 + (192461368558471629/146000000000000000000000000000000 : ℝ)*base70 + (1306221276186471629/146000000000000000000000000000000 : ℝ)*base72 + (20915100620137/1460000000000000000000000000 : ℝ)*base73 + (452918993614471629/146000000000000000000000000000000 : ℝ)*base76 + (478181663570471629/146000000000000000000000000000000 : ℝ)*base78 + (2289855380856471629/146000000000000000000000000000000 : ℝ)*base80 + (6900205835303/1460000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4700119/625000000000000000000 : ℝ)*base90 + (4700119/625000000000000000000 : ℝ)*base92 + (4700119/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-10559/12500 : ℝ) ≤ (-49330219566641287017436022755629/58400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20286313/25000000000000 : ℝ)*(lower0) + (152117851/100000000000000 : ℝ)*(lower2) + (2832841/2000000000000 : ℝ)*(upper5) + (674528105891133/20000000000000 : ℝ)*(major0) + (674528105891133/20000000000000 : ℝ)*(major1) + (674528105891133/20000000000000 : ℝ)*(major2) + (1214350501/25000000000000 : ℝ)*(sp4) + (272003212707/100000000000000 : ℝ)*(sp5) + (33154854059/20000000000000 : ℝ)*(sp7) + (1117814633/6250000000000 : ℝ)*(sp8) + (4610792286581209/100000000000000 : ℝ)*(sp12) + (2305271512902317/50000000000000 : ℝ)*(sp13) + (4610815029017341/100000000000000 : ℝ)*(sp14) + (1081228386820587/50000000000000 : ℝ)*(sp15) + (2162622547911469/100000000000000 : ℝ)*(f.failure) + (4610815029017341/100000000000000 : ℝ)*(f.sum) + (740748644849/233600000000000000000000000 : ℝ)*base66 + (2371918922552968543/116800000000000000000000000000000 : ℝ)*base68 + (555237077296631457/116800000000000000000000000000000 : ℝ)*base69 + (134505163373768543/116800000000000000000000000000000 : ℝ)*base72 + (12067564441201/233600000000000000000000000 : ℝ)*base74 + (505994802087031457/116800000000000000000000000000000 : ℝ)*base75 + (90232085063368543/116800000000000000000000000000000 : ℝ)*base78 + (167283363376968543/116800000000000000000000000000000 : ℝ)*base80 + (3164780033461/1168000000000000000000000000 : ℝ)*base82 + (14506521/5000000000000000000000 : ℝ)*base89 + (14506521/5000000000000000000000 : ℝ)*base91 + (14506521/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1373_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62869/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29501/50000 : ℝ) else (40067/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10559/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1373_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1373_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62869/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29501/50000 : ℝ) else (40067/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10559/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1373_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1373_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1373_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1083/256 : ℝ) ≤ p) (hpb : p ≤ (4333/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77975709/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62869/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29501/50000 : ℝ) else (40067/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10559/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1373_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
