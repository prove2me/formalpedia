-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1507_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:19.669714+00:00
-- url     : https://prove2.me/submissions/04e985b1-c66c-4376-b95d-5a7f02e69bae

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
theorem support_rectangle_w1507_s3_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-187490041/1000000000 : ℝ)*x 0 + (1087470573/2000000000 : ℝ)*x 1 + (208570439/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187490041/1000000000 : ℝ)^4511 ≤ (11467781327763/100000000000000 : ℝ)^3487 := by
    have hnat : (187490041 : ℕ)^4511*100000000000000^3487 ≤ 11467781327763^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187490041 1000000000 11467781327763 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087470573/2000000000 : ℝ)^4511 ≤ (45465381692961/100000000000000 : ℝ)^3487 := by
    have hnat : (1087470573 : ℕ)^4511*100000000000000^3487 ≤ 45465381692961^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087470573 2000000000 45465381692961 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208570439/400000000 : ℝ)^4511 ≤ (10766709239827/25000000000000 : ℝ)^3487 := by
    have hnat : (208570439 : ℕ)^4511*25000000000000^3487 ≤ 10766709239827^3487*400000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208570439 400000000 10766709239827 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187490041/1000000000 : ℝ), (1087470573/2000000000 : ℝ), (208570439/400000000 : ℝ)] ![(11467781327763/100000000000000 : ℝ), (45465381692961/100000000000000 : ℝ), (10766709239827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187490041/1000000000 : ℝ)|^4511 ≤ (11467781327763/100000000000000 : ℝ)^3487
        have hw : |(-187490041/1000000000 : ℝ)|=(187490041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087470573/2000000000 : ℝ)|^4511 ≤ (45465381692961/100000000000000 : ℝ)^3487
        have hw : |(1087470573/2000000000 : ℝ)|=(1087470573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208570439/400000000 : ℝ)|^4511 ≤ (10766709239827/25000000000000 : ℝ)^3487
        have hw : |(208570439/400000000 : ℝ)|=(208570439/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42822193/80000000 : ℝ)*x 0 + (-1989251061/10000000000 : ℝ)*x 1 + (5214260981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42822193/80000000 : ℝ)^4511 ≤ (8910515050547/20000000000000 : ℝ)^3487 := by
    have hnat : (42822193 : ℕ)^4511*20000000000000^3487 ≤ 8910515050547^3487*80000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42822193 80000000 8910515050547 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989251061/10000000000 : ℝ)^4511 ≤ (3095146928023/25000000000000 : ℝ)^3487 := by
    have hnat : (1989251061 : ℕ)^4511*25000000000000^3487 ≤ 3095146928023^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989251061 10000000000 3095146928023 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214260981/10000000000 : ℝ)^4511 ≤ (43066837023417/100000000000000 : ℝ)^3487 := by
    have hnat : (5214260981 : ℕ)^4511*100000000000000^3487 ≤ 43066837023417^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214260981 10000000000 43066837023417 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42822193/80000000 : ℝ), (-1989251061/10000000000 : ℝ), (5214260981/10000000000 : ℝ)] ![(8910515050547/20000000000000 : ℝ), (3095146928023/25000000000000 : ℝ), (43066837023417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42822193/80000000 : ℝ)|^4511 ≤ (8910515050547/20000000000000 : ℝ)^3487
        have hw : |(42822193/80000000 : ℝ)|=(42822193/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989251061/10000000000 : ℝ)|^4511 ≤ (3095146928023/25000000000000 : ℝ)^3487
        have hw : |(-1989251061/10000000000 : ℝ)|=(1989251061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214260981/10000000000 : ℝ)|^4511 ≤ (43066837023417/100000000000000 : ℝ)^3487
        have hw : |(5214260981/10000000000 : ℝ)|=(5214260981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338193677/2500000000 : ℝ)*x 0 + (5214260523/10000000000 : ℝ)*x 1 + (-1989250889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338193677/2500000000 : ℝ)^4511 ≤ (22276290765093/50000000000000 : ℝ)^3487 := by
    have hnat : (1338193677 : ℕ)^4511*50000000000000^3487 ≤ 22276290765093^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338193677 2500000000 22276290765093 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214260523/10000000000 : ℝ)^4511 ≤ (21533416064863/50000000000000 : ℝ)^3487 := by
    have hnat : (5214260523 : ℕ)^4511*50000000000000^3487 ≤ 21533416064863^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214260523 10000000000 21533416064863 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989250889/10000000000 : ℝ)^4511 ≤ (12380586327247/100000000000000 : ℝ)^3487 := by
    have hnat : (1989250889 : ℕ)^4511*100000000000000^3487 ≤ 12380586327247^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989250889 10000000000 12380586327247 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338193677/2500000000 : ℝ), (5214260523/10000000000 : ℝ), (-1989250889/10000000000 : ℝ)] ![(22276290765093/50000000000000 : ℝ), (21533416064863/50000000000000 : ℝ), (12380586327247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338193677/2500000000 : ℝ)|^4511 ≤ (22276290765093/50000000000000 : ℝ)^3487
        have hw : |(1338193677/2500000000 : ℝ)|=(1338193677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214260523/10000000000 : ℝ)|^4511 ≤ (21533416064863/50000000000000 : ℝ)^3487
        have hw : |(5214260523/10000000000 : ℝ)|=(5214260523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989250889/10000000000 : ℝ)|^4511 ≤ (12380586327247/100000000000000 : ℝ)^3487
        have hw : |(-1989250889/10000000000 : ℝ)|=(1989250889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135888169/5000000000 : ℝ)*x 0 + (1006516247/2500000000 : ℝ)*x 1 + (2265082041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135888169/5000000000 : ℝ)^4511 ≤ (16638041413511/50000000000000 : ℝ)^3487 := by
    have hnat : (2135888169 : ℕ)^4511*50000000000000^3487 ≤ 16638041413511^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135888169 5000000000 16638041413511 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006516247/2500000000 : ℝ)^4511 ≤ (15410588236643/50000000000000 : ℝ)^3487 := by
    have hnat : (1006516247 : ℕ)^4511*50000000000000^3487 ≤ 15410588236643^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006516247 2500000000 15410588236643 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265082041/5000000000 : ℝ)^4511 ≤ (1436109627179/4000000000000 : ℝ)^3487 := by
    have hnat : (2265082041 : ℕ)^4511*4000000000000^3487 ≤ 1436109627179^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265082041 5000000000 1436109627179 4000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135888169/5000000000 : ℝ), (1006516247/2500000000 : ℝ), (2265082041/5000000000 : ℝ)] ![(16638041413511/50000000000000 : ℝ), (15410588236643/50000000000000 : ℝ), (1436109627179/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135888169/5000000000 : ℝ)|^4511 ≤ (16638041413511/50000000000000 : ℝ)^3487
        have hw : |(2135888169/5000000000 : ℝ)|=(2135888169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006516247/2500000000 : ℝ)|^4511 ≤ (15410588236643/50000000000000 : ℝ)^3487
        have hw : |(1006516247/2500000000 : ℝ)|=(1006516247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265082041/5000000000 : ℝ)|^4511 ≤ (1436109627179/4000000000000 : ℝ)^3487
        have hw : |(2265082041/5000000000 : ℝ)|=(2265082041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1874931427/10000000000 : ℝ)*x 0 + (5215442981/10000000000 : ℝ)*x 1 + (5436162547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1874931427/10000000000 : ℝ)^4511 ≤ (11468026755093/100000000000000 : ℝ)^3487 := by
    have hnat : (1874931427 : ℕ)^4511*100000000000000^3487 ≤ 11468026755093^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874931427 10000000000 11468026755093 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215442981/10000000000 : ℝ)^4511 ≤ (43079467013891/100000000000000 : ℝ)^3487 := by
    have hnat : (5215442981 : ℕ)^4511*100000000000000^3487 ≤ 43079467013891^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215442981 10000000000 43079467013891 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436162547/10000000000 : ℝ)^4511 ≤ (909050124369/2000000000000 : ℝ)^3487 := by
    have hnat : (5436162547 : ℕ)^4511*2000000000000^3487 ≤ 909050124369^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436162547 10000000000 909050124369 2000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1874931427/10000000000 : ℝ), (5215442981/10000000000 : ℝ), (5436162547/10000000000 : ℝ)] ![(11468026755093/100000000000000 : ℝ), (43079467013891/100000000000000 : ℝ), (909050124369/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1874931427/10000000000 : ℝ)|^4511 ≤ (11468026755093/100000000000000 : ℝ)^3487
        have hw : |(-1874931427/10000000000 : ℝ)|=(1874931427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215442981/10000000000 : ℝ)|^4511 ≤ (43079467013891/100000000000000 : ℝ)^3487
        have hw : |(5215442981/10000000000 : ℝ)|=(5215442981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436162547/10000000000 : ℝ)|^4511 ≤ (909050124369/2000000000000 : ℝ)^3487
        have hw : |(5436162547/10000000000 : ℝ)|=(5436162547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_5 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294252503/10000000000 : ℝ)*x 0 + (-1767349259/10000000000 : ℝ)*x 1 + (679520343/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294252503/10000000000 : ℝ)^4511 ≤ (5490432250703/12500000000000 : ℝ)^3487 := by
    have hnat : (5294252503 : ℕ)^4511*12500000000000^3487 ≤ 5490432250703^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294252503 10000000000 5490432250703 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1767349259/10000000000 : ℝ)^4511 ≤ (10624033628809/100000000000000 : ℝ)^3487 := by
    have hnat : (1767349259 : ℕ)^4511*100000000000000^3487 ≤ 10624033628809^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767349259 10000000000 10624033628809 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679520343/1250000000 : ℝ)^4511 ≤ (45452508349299/100000000000000 : ℝ)^3487 := by
    have hnat : (679520343 : ℕ)^4511*100000000000000^3487 ≤ 45452508349299^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679520343 1250000000 45452508349299 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294252503/10000000000 : ℝ), (-1767349259/10000000000 : ℝ), (679520343/1250000000 : ℝ)] ![(5490432250703/12500000000000 : ℝ), (10624033628809/100000000000000 : ℝ), (45452508349299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294252503/10000000000 : ℝ)|^4511 ≤ (5490432250703/12500000000000 : ℝ)^3487
        have hw : |(5294252503/10000000000 : ℝ)|=(5294252503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1767349259/10000000000 : ℝ)|^4511 ≤ (10624033628809/100000000000000 : ℝ)^3487
        have hw : |(-1767349259/10000000000 : ℝ)|=(1767349259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679520343/1250000000 : ℝ)|^4511 ≤ (45452508349299/100000000000000 : ℝ)^3487
        have hw : |(679520343/1250000000 : ℝ)|=(679520343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_6 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294252727/10000000000 : ℝ)*x 0 + (2718081221/5000000000 : ℝ)*x 1 + (-176734937/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294252727/10000000000 : ℝ)^4511 ≤ (4392346040977/10000000000000 : ℝ)^3487 := by
    have hnat : (5294252727 : ℕ)^4511*10000000000000^3487 ≤ 4392346040977^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294252727 10000000000 4392346040977 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718081221/5000000000 : ℝ)^4511 ≤ (45452505082719/100000000000000 : ℝ)^3487 := by
    have hnat : (2718081221 : ℕ)^4511*100000000000000^3487 ≤ 45452505082719^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718081221 5000000000 45452505082719 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176734937/1000000000 : ℝ)^4511 ≤ (1328004311501/12500000000000 : ℝ)^3487 := by
    have hnat : (176734937 : ℕ)^4511*12500000000000^3487 ≤ 1328004311501^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176734937 1000000000 1328004311501 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294252727/10000000000 : ℝ), (2718081221/5000000000 : ℝ), (-176734937/1000000000 : ℝ)] ![(4392346040977/10000000000000 : ℝ), (45452505082719/100000000000000 : ℝ), (1328004311501/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294252727/10000000000 : ℝ)|^4511 ≤ (4392346040977/10000000000000 : ℝ)^3487
        have hw : |(5294252727/10000000000 : ℝ)|=(5294252727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718081221/5000000000 : ℝ)|^4511 ≤ (45452505082719/100000000000000 : ℝ)^3487
        have hw : |(2718081221/5000000000 : ℝ)|=(2718081221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-176734937/1000000000 : ℝ)|^4511 ≤ (1328004311501/12500000000000 : ℝ)^3487
        have hw : |(-176734937/1000000000 : ℝ)|=(176734937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_7 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271848277/10000000000 : ℝ)*x 0 + (4527493657/10000000000 : ℝ)*x 1 + (4028755841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271848277/10000000000 : ℝ)^4511 ≤ (16638403890169/50000000000000 : ℝ)^3487 := by
    have hnat : (4271848277 : ℕ)^4511*50000000000000^3487 ≤ 16638403890169^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271848277 10000000000 16638403890169 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527493657/10000000000 : ℝ)^4511 ≤ (17937682108207/50000000000000 : ℝ)^3487 := by
    have hnat : (4527493657 : ℕ)^4511*50000000000000^3487 ≤ 17937682108207^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527493657 10000000000 17937682108207 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028755841/10000000000 : ℝ)^4511 ≤ (6169565597579/20000000000000 : ℝ)^3487 := by
    have hnat : (4028755841 : ℕ)^4511*20000000000000^3487 ≤ 6169565597579^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028755841 10000000000 6169565597579 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271848277/10000000000 : ℝ), (4527493657/10000000000 : ℝ), (4028755841/10000000000 : ℝ)] ![(16638403890169/50000000000000 : ℝ), (17937682108207/50000000000000 : ℝ), (6169565597579/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271848277/10000000000 : ℝ)|^4511 ≤ (16638403890169/50000000000000 : ℝ)^3487
        have hw : |(4271848277/10000000000 : ℝ)|=(4271848277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527493657/10000000000 : ℝ)|^4511 ≤ (17937682108207/50000000000000 : ℝ)^3487
        have hw : |(4527493657/10000000000 : ℝ)|=(4527493657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028755841/10000000000 : ℝ)|^4511 ≤ (6169565597579/20000000000000 : ℝ)^3487
        have hw : |(4028755841/10000000000 : ℝ)|=(4028755841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_8 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2825183/2000000000 : ℝ)*x 0 + (1170185959/2000000000 : ℝ)*x 1 + (731400201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2825183/2000000000 : ℝ)^4511 ≤ (20562895327/100000000000000 : ℝ)^3487 := by
    have hnat : (2825183 : ℕ)^4511*100000000000000^3487 ≤ 20562895327^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825183 2000000000 20562895327 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170185959/2000000000 : ℝ)^4511 ≤ (24994108209937/50000000000000 : ℝ)^3487 := by
    have hnat : (1170185959 : ℕ)^4511*50000000000000^3487 ≤ 24994108209937^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170185959 2000000000 24994108209937 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731400201/1250000000 : ℝ)^4511 ≤ (9998244135013/20000000000000 : ℝ)^3487 := by
    have hnat : (731400201 : ℕ)^4511*20000000000000^3487 ≤ 9998244135013^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731400201 1250000000 9998244135013 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2825183/2000000000 : ℝ), (1170185959/2000000000 : ℝ), (731400201/1250000000 : ℝ)] ![(20562895327/100000000000000 : ℝ), (24994108209937/50000000000000 : ℝ), (9998244135013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2825183/2000000000 : ℝ)|^4511 ≤ (20562895327/100000000000000 : ℝ)^3487
        have hw : |(-2825183/2000000000 : ℝ)|=(2825183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1170185959/2000000000 : ℝ)|^4511 ≤ (24994108209937/50000000000000 : ℝ)^3487
        have hw : |(1170185959/2000000000 : ℝ)|=(1170185959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(731400201/1250000000 : ℝ)|^4511 ≤ (9998244135013/20000000000000 : ℝ)^3487
        have hw : |(731400201/1250000000 : ℝ)|=(731400201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_9 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (497079401/5000000000 : ℝ)*x 0 + (-870461599/2000000000 : ℝ)*x 1 + (6652812/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497079401/5000000000 : ℝ)^4511 ≤ (1009430533861/20000000000000 : ℝ)^3487 := by
    have hnat : (497079401 : ℕ)^4511*20000000000000^3487 ≤ 1009430533861^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497079401 5000000000 1009430533861 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (870461599/2000000000 : ℝ)^4511 ≤ (34089861719381/100000000000000 : ℝ)^3487 := by
    have hnat : (870461599 : ℕ)^4511*100000000000000^3487 ≤ 34089861719381^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870461599 2000000000 34089861719381 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6652812/9765625 : ℝ)^4511 ≤ (60862985592937/100000000000000 : ℝ)^3487 := by
    have hnat : (6652812 : ℕ)^4511*100000000000000^3487 ≤ 60862985592937^3487*9765625^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6652812 9765625 60862985592937 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(497079401/5000000000 : ℝ), (-870461599/2000000000 : ℝ), (6652812/9765625 : ℝ)] ![(1009430533861/20000000000000 : ℝ), (34089861719381/100000000000000 : ℝ), (60862985592937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(497079401/5000000000 : ℝ)|^4511 ≤ (1009430533861/20000000000000 : ℝ)^3487
        have hw : |(497079401/5000000000 : ℝ)|=(497079401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-870461599/2000000000 : ℝ)|^4511 ≤ (34089861719381/100000000000000 : ℝ)^3487
        have hw : |(-870461599/2000000000 : ℝ)|=(870461599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6652812/9765625 : ℝ)|^4511 ≤ (60862985592937/100000000000000 : ℝ)^3487
        have hw : |(6652812/9765625 : ℝ)|=(6652812/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_10 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (496643389/5000000000 : ℝ)*x 0 + (272414883/400000000 : ℝ)*x 1 + (-272204781/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496643389/5000000000 : ℝ)^4511 ≤ (5041426238093/100000000000000 : ℝ)^3487 := by
    have hnat : (496643389 : ℕ)^4511*100000000000000^3487 ≤ 5041426238093^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496643389 5000000000 5041426238093 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272414883/400000000 : ℝ)^4511 ≤ (7604828748989/12500000000000 : ℝ)^3487 := by
    have hnat : (272414883 : ℕ)^4511*12500000000000^3487 ≤ 7604828748989^3487*400000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272414883 400000000 7604828748989 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272204781/625000000 : ℝ)^4511 ≤ (3411994375227/10000000000000 : ℝ)^3487 := by
    have hnat : (272204781 : ℕ)^4511*10000000000000^3487 ≤ 3411994375227^3487*625000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272204781 625000000 3411994375227 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(496643389/5000000000 : ℝ), (272414883/400000000 : ℝ), (-272204781/625000000 : ℝ)] ![(5041426238093/100000000000000 : ℝ), (7604828748989/12500000000000 : ℝ), (3411994375227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(496643389/5000000000 : ℝ)|^4511 ≤ (5041426238093/100000000000000 : ℝ)^3487
        have hw : |(496643389/5000000000 : ℝ)|=(496643389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272414883/400000000 : ℝ)|^4511 ≤ (7604828748989/12500000000000 : ℝ)^3487
        have hw : |(272414883/400000000 : ℝ)|=(272414883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272204781/625000000 : ℝ)|^4511 ≤ (3411994375227/10000000000000 : ℝ)^3487
        have hw : |(-272204781/625000000 : ℝ)|=(272204781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s3_11 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1484077813/10000000000 : ℝ)*x 0 + (54635057/100000000 : ℝ)*x 1 + (2733042281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1484077813/10000000000 : ℝ)^4511 ≤ (2118775031713/25000000000000 : ℝ)^3487 := by
    have hnat : (1484077813 : ℕ)^4511*25000000000000^3487 ≤ 2118775031713^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1484077813 10000000000 2118775031713 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54635057/100000000 : ℝ)^4511 ≤ (45748481280251/100000000000000 : ℝ)^3487 := by
    have hnat : (54635057 : ℕ)^4511*100000000000000^3487 ≤ 45748481280251^3487*100000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54635057 100000000 45748481280251 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733042281/5000000000 : ℝ)^4511 ≤ (22888209287777/50000000000000 : ℝ)^3487 := by
    have hnat : (2733042281 : ℕ)^4511*50000000000000^3487 ≤ 22888209287777^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733042281 5000000000 22888209287777 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1484077813/10000000000 : ℝ), (54635057/100000000 : ℝ), (2733042281/5000000000 : ℝ)] ![(2118775031713/25000000000000 : ℝ), (45748481280251/100000000000000 : ℝ), (22888209287777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1484077813/10000000000 : ℝ)|^4511 ≤ (2118775031713/25000000000000 : ℝ)^3487
        have hw : |(1484077813/10000000000 : ℝ)|=(1484077813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54635057/100000000 : ℝ)|^4511 ≤ (45748481280251/100000000000000 : ℝ)^3487
        have hw : |(54635057/100000000 : ℝ)|=(54635057/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733042281/5000000000 : ℝ)|^4511 ≤ (22888209287777/50000000000000 : ℝ)^3487
        have hw : |(2733042281/5000000000 : ℝ)|=(2733042281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1083/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15553/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1001/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2081/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1001/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2081/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1001/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2081/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1001/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2081/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1001/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2081/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1001/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2081/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2081/20000 : ℝ) ^ (4509/1024 : ℝ) ≤ (4705460245772797/100000000000000000000 : ℝ) := by
    have hpowers : (2081/20000 : ℝ)^4509 ≤ (4705460245772797/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2081 : ℕ)^4509*100000000000000000000^1024 ≤ 4705460245772797^1024*20000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2081 20000 4705460245772797 100000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2081/20000 : ℝ)) (X := (4705460245772797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1001/6250 : ℝ) ^ (4509/1024 : ℝ) ≤ (3069705970233/9765625000000000 : ℝ) := by
    have hpowers : (1001/6250 : ℝ)^4509 ≤ (3069705970233/9765625000000000 : ℝ)^1024 := by
      have hnat : (1001 : ℕ)^4509*9765625000000000^1024 ≤ 3069705970233^1024*6250^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001 6250 3069705970233 9765625000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1001/6250 : ℝ)) (X := (3069705970233/9765625000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004705460245772797/50000000000000000000 : ℝ) ≤ (1000021371550517/1000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (50004705460245772797/50000000000000000000 : ℝ)^1024 ≤ (1000021371550517/1000000000000000 : ℝ)^4509 := by
      have hnat : (50004705460245772797 : ℕ)^1024*1000000000000000^4509 ≤ 1000021371550517^4509*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004705460245772797 50000000000000000000 1000021371550517 1000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021371550517/1000000000000000 : ℝ)) (X := (50004705460245772797/50000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036139249380958717/100000000000000000000 : ℝ) ≤ (5000410306322171/5000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (100036139249380958717/100000000000000000000 : ℝ)^1024 ≤ (5000410306322171/5000000000000000 : ℝ)^4509 := by
      have hnat : (100036139249380958717 : ℕ)^1024*5000000000000000^4509 ≤ 5000410306322171^4509*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036139249380958717 100000000000000000000 5000410306322171 5000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000410306322171/5000000000000000 : ℝ)) (X := (100036139249380958717/100000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (4885882205970233/4882812500000000 : ℝ) ≤ (5000713754891757/5000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (4885882205970233/4882812500000000 : ℝ)^1024 ≤ (5000713754891757/5000000000000000 : ℝ)^4509 := by
      have hnat : (4885882205970233 : ℕ)^1024*5000000000000000^4509 ≤ 5000713754891757^4509*4882812500000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4885882205970233 4882812500000000 5000713754891757 5000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000713754891757/5000000000000000 : ℝ)) (X := (4885882205970233/4882812500000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4705460245772797/100000000000000000000 : ℝ) ≤ ((1121971392564666791/1122200000000000000 : ℝ)+2*(151724284793/140275000000000 : ℝ)*(2081/20000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (1121971392564666791/1122200000000000000 : ℝ)+2*(151724284793/140275000000000 : ℝ)*(2081/20000 : ℝ)=(1000021371550517/1000000000000000 : ℝ) by norm_num, show 1+2*(4705460245772797/100000000000000000000 : ℝ)=(50004705460245772797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3069705970233/9765625000000000 : ℝ)+(4705460245772797/100000000000000000000 : ℝ) ≤ ((1121971392564666791/1122200000000000000 : ℝ)+(151724284793/140275000000000 : ℝ)*((1001/6250 : ℝ)+(2081/20000 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (1121971392564666791/1122200000000000000 : ℝ)+(151724284793/140275000000000 : ℝ)*((1001/6250 : ℝ)+(2081/20000 : ℝ))=(5000410306322171/5000000000000000 : ℝ) by norm_num, show 1+(3069705970233/9765625000000000 : ℝ)+(4705460245772797/100000000000000000000 : ℝ)=(100036139249380958717/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3069705970233/9765625000000000 : ℝ) ≤ ((1121971392564666791/1122200000000000000 : ℝ)+2*(151724284793/140275000000000 : ℝ)*(1001/6250 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (1121971392564666791/1122200000000000000 : ℝ)+2*(151724284793/140275000000000 : ℝ)*(1001/6250 : ℝ)=(5000713754891757/5000000000000000 : ℝ) by norm_num, show 1+2*(3069705970233/9765625000000000 : ℝ)=(4885882205970233/4882812500000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1121971392564666791/1122200000000000000 : ℝ)*(X 1 0+X 2 0)+(151724284793/140275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (2081/20000 : ℝ)) (hi := (1001/6250 : ℝ)) (c := (1121971392564666791/1122200000000000000 : ℝ)) (alpha := (151724284793/140275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1121971392564666791/1122200000000000000 : ℝ)*(X 0 1+X 2 1)+(151724284793/140275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (2081/20000 : ℝ)) (hi := (1001/6250 : ℝ)) (c := (1121971392564666791/1122200000000000000 : ℝ)) (alpha := (151724284793/140275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1121971392564666791/1122200000000000000 : ℝ)*(X 0 2+X 1 2)+(151724284793/140275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (2081/20000 : ℝ)) (hi := (1001/6250 : ℝ)) (c := (1121971392564666791/1122200000000000000 : ℝ)) (alpha := (151724284793/140275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-187490041/1000000000 : ℝ)*X 0 0+(1087470573/2000000000 : ℝ)*X 0 1+(208570439/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42822193/80000000 : ℝ)*X 1 0+(-1989251061/10000000000 : ℝ)*X 1 1+(5214260981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338193677/2500000000 : ℝ)*X 2 0+(5214260523/10000000000 : ℝ)*X 2 1+(-1989250889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2135888169/5000000000 : ℝ)*X 0 0+(1006516247/2500000000 : ℝ)*X 0 1+(2265082041/5000000000 : ℝ)*X 0 2+(2135888169/5000000000 : ℝ)*X 1 0+(1006516247/2500000000 : ℝ)*X 1 1+(2265082041/5000000000 : ℝ)*X 1 2+(2135888169/5000000000 : ℝ)*X 2 0+(1006516247/2500000000 : ℝ)*X 2 1+(2265082041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1874931427/10000000000 : ℝ)*X 0 0+(5215442981/10000000000 : ℝ)*X 0 1+(5436162547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294252503/10000000000 : ℝ)*X 1 0+(-1767349259/10000000000 : ℝ)*X 1 1+(679520343/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294252727/10000000000 : ℝ)*X 2 0+(2718081221/5000000000 : ℝ)*X 2 1+(-176734937/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4271848277/10000000000 : ℝ)*X 0 0+(4527493657/10000000000 : ℝ)*X 0 1+(4028755841/10000000000 : ℝ)*X 0 2+(4271848277/10000000000 : ℝ)*X 1 0+(4527493657/10000000000 : ℝ)*X 1 1+(4028755841/10000000000 : ℝ)*X 1 2+(4271848277/10000000000 : ℝ)*X 2 0+(4527493657/10000000000 : ℝ)*X 2 1+(4028755841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2825183/2000000000 : ℝ)*X 0 0+(1170185959/2000000000 : ℝ)*X 0 1+(731400201/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((497079401/5000000000 : ℝ)*X 1 0+(-870461599/2000000000 : ℝ)*X 1 1+(6652812/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((496643389/5000000000 : ℝ)*X 2 0+(272414883/400000000 : ℝ)*X 2 1+(-272204781/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1484077813/10000000000 : ℝ)*X 0 0+(54635057/100000000 : ℝ)*X 0 1+(2733042281/5000000000 : ℝ)*X 0 2+(1484077813/10000000000 : ℝ)*X 1 0+(54635057/100000000 : ℝ)*X 1 1+(2733042281/5000000000 : ℝ)*X 1 2+(1484077813/10000000000 : ℝ)*X 2 0+(54635057/100000000 : ℝ)*X 2 1+(2733042281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1618784353482097161564339/438359375000000000000000000000 : ℝ) := by norm_num
    linear_combination (208893077/100000000000000 : ℝ)*(lower3) + (404137123854769/12500000000000 : ℝ)*(major0) + (404137123854769/12500000000000 : ℝ)*(major1) + (404137123854769/12500000000000 : ℝ)*(major2) + (448245075907831/10000000000000 : ℝ)*(sp0) + (224122691631249/5000000000000 : ℝ)*(sp1) + (448244537966927/10000000000000 : ℝ)*(sp2) + (991869183738877/50000000000000 : ℝ)*(sp3) + (397149377/100000000000000 : ℝ)*(sp5) + (4178761253/50000000000000 : ℝ)*(sp6) + (869409643/25000000000000 : ℝ)*(sp8) + (277701/4000000000000 : ℝ)*(sp9) + (249762553/50000000000000 : ℝ)*(sp10) + (627193753/50000000000000 : ℝ)*(sp11) + (99186981093263/5000000000000 : ℝ)*(f.failure) + (2241227118358441/50000000000000 : ℝ)*(f.sum) + (35192481704447/14027500000000000000000000000 : ℝ)*base65 + (13368063785342721/14027500000000000000000000000000 : ℝ)*base68 + (56121333361402721/14027500000000000000000000000000 : ℝ)*base70 + (76404217223990221/14027500000000000000000000000000 : ℝ)*base72 + (61092553290663/14027500000000000000000000000 : ℝ)*base74 + (68695122043057721/14027500000000000000000000000000 : ℝ)*base76 + (47330923250987721/14027500000000000000000000000000 : ℝ)*base78 + (7476072878802279/14027500000000000000000000000000 : ℝ)*base79 + (47083388316287/14027500000000000000000000000 : ℝ)*base81 + (2066541/500000000000000000000 : ℝ)*base89 + (2066541/500000000000000000000 : ℝ)*base91 + (2066541/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17713692972931185289689/5611000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20227391/50000000000000 : ℝ)*(lower5) + (653569839781151/20000000000000 : ℝ)*(major0) + (653569839781151/20000000000000 : ℝ)*(major1) + (653569839781151/20000000000000 : ℝ)*(major2) + (424453767/10000000000000 : ℝ)*(sp1) + (42897329/12500000000000 : ℝ)*(sp2) + (4530635253902079/100000000000000 : ℝ)*(sp4) + (4530631263567359/100000000000000 : ℝ)*(sp5) + (2265317491040927/50000000000000 : ℝ)*(sp6) + (1002531052344679/50000000000000 : ℝ)*(sp7) + (207639761/50000000000000 : ℝ)*(sp8) + (161076571/100000000000000 : ℝ)*(sp9) + (68784223/20000000000000 : ℝ)*(sp10) + (259354301/50000000000000 : ℝ)*(sp11) + (50126565584949/2500000000000 : ℝ)*(f.failure) + (4530635669181601/100000000000000 : ℝ)*(f.sum) + (3431210911947/5611000000000000000000000000 : ℝ)*base66 + (61100333883220441/22444000000000000000000000000000 : ℝ)*base67 + (160253613782603559/22444000000000000000000000000000 : ℝ)*base70 + (50421461491116441/22444000000000000000000000000000 : ℝ)*base71 + (39349874475631/2805500000000000000000000000 : ℝ)*base73 + (105265719654696441/22444000000000000000000000000000 : ℝ)*base75 + (18315679131543559/22444000000000000000000000000000 : ℝ)*base78 + (144332294538939559/22444000000000000000000000000000 : ℝ)*base80 + (17892428763849/2805500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1119743/250000000000000000000 : ℝ)*base89 + (1119743/250000000000000000000 : ℝ)*base91 + (1119743/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1507_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15553/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1507_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1507_s4_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875365821/10000000000 : ℝ)*x 0 + (543430771/1000000000 : ℝ)*x 1 + (1304249673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875365821/10000000000 : ℝ)^4511 ≤ (1147146409737/10000000000000 : ℝ)^3487 := by
    have hnat : (1875365821 : ℕ)^4511*10000000000000^3487 ≤ 1147146409737^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875365821 10000000000 1147146409737 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543430771/1000000000 : ℝ)^4511 ≤ (9086488880231/20000000000000 : ℝ)^3487 := by
    have hnat : (543430771 : ℕ)^4511*20000000000000^3487 ≤ 9086488880231^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543430771 1000000000 9086488880231 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304249673/2500000000 : ℝ)^4511 ≤ (2154804574449/5000000000000 : ℝ)^3487 := by
    have hnat : (1304249673 : ℕ)^4511*5000000000000^3487 ≤ 2154804574449^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304249673 2500000000 2154804574449 5000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875365821/10000000000 : ℝ), (543430771/1000000000 : ℝ), (1304249673/2500000000 : ℝ)] ![(1147146409737/10000000000000 : ℝ), (9086488880231/20000000000000 : ℝ), (2154804574449/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875365821/10000000000 : ℝ)|^4511 ≤ (1147146409737/10000000000000 : ℝ)^3487
        have hw : |(-1875365821/10000000000 : ℝ)|=(1875365821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543430771/1000000000 : ℝ)|^4511 ≤ (9086488880231/20000000000000 : ℝ)^3487
        have hw : |(543430771/1000000000 : ℝ)|=(543430771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304249673/2500000000 : ℝ)|^4511 ≤ (2154804574449/5000000000000 : ℝ)^3487
        have hw : |(1304249673/2500000000 : ℝ)|=(1304249673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s4_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337994581/2500000000 : ℝ)*x 0 + (-397336607/2000000000 : ℝ)*x 1 + (2608498713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337994581/2500000000 : ℝ)^4511 ≤ (22272003327307/50000000000000 : ℝ)^3487 := by
    have hnat : (1337994581 : ℕ)^4511*50000000000000^3487 ≤ 22272003327307^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337994581 2500000000 22272003327307 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397336607/2000000000 : ℝ)^4511 ≤ (12359915373723/100000000000000 : ℝ)^3487 := by
    have hnat : (397336607 : ℕ)^4511*100000000000000^3487 ≤ 12359915373723^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397336607 2000000000 12359915373723 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608498713/5000000000 : ℝ)^4511 ≤ (2693504872487/6250000000000 : ℝ)^3487 := by
    have hnat : (2608498713 : ℕ)^4511*6250000000000^3487 ≤ 2693504872487^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608498713 5000000000 2693504872487 6250000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337994581/2500000000 : ℝ), (-397336607/2000000000 : ℝ), (2608498713/5000000000 : ℝ)] ![(22272003327307/50000000000000 : ℝ), (12359915373723/100000000000000 : ℝ), (2693504872487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337994581/2500000000 : ℝ)|^4511 ≤ (22272003327307/50000000000000 : ℝ)^3487
        have hw : |(1337994581/2500000000 : ℝ)|=(1337994581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397336607/2000000000 : ℝ)|^4511 ≤ (12359915373723/100000000000000 : ℝ)^3487
        have hw : |(-397336607/2000000000 : ℝ)|=(397336607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608498713/5000000000 : ℝ)|^4511 ≤ (2693504872487/6250000000000 : ℝ)^3487
        have hw : |(2608498713/5000000000 : ℝ)|=(2608498713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s4_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070395537/2000000000 : ℝ)*x 0 + (5216998633/10000000000 : ℝ)*x 1 + (-1986682287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070395537/2000000000 : ℝ)^4511 ≤ (44543999774483/100000000000000 : ℝ)^3487 := by
    have hnat : (1070395537 : ℕ)^4511*100000000000000^3487 ≤ 44543999774483^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070395537 2000000000 44543999774483 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216998633/10000000000 : ℝ)^4511 ≤ (43096090858473/100000000000000 : ℝ)^3487 := by
    have hnat : (5216998633 : ℕ)^4511*100000000000000^3487 ≤ 43096090858473^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216998633 10000000000 43096090858473 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986682287/10000000000 : ℝ)^4511 ≤ (1544988669193/12500000000000 : ℝ)^3487 := by
    have hnat : (1986682287 : ℕ)^4511*12500000000000^3487 ≤ 1544988669193^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986682287 10000000000 1544988669193 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070395537/2000000000 : ℝ), (5216998633/10000000000 : ℝ), (-1986682287/10000000000 : ℝ)] ![(44543999774483/100000000000000 : ℝ), (43096090858473/100000000000000 : ℝ), (1544988669193/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070395537/2000000000 : ℝ)|^4511 ≤ (44543999774483/100000000000000 : ℝ)^3487
        have hw : |(1070395537/2000000000 : ℝ)|=(1070395537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216998633/10000000000 : ℝ)|^4511 ≤ (43096090858473/100000000000000 : ℝ)^3487
        have hw : |(5216998633/10000000000 : ℝ)|=(5216998633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986682287/10000000000 : ℝ)|^4511 ≤ (1544988669193/12500000000000 : ℝ)^3487
        have hw : |(-1986682287/10000000000 : ℝ)|=(1986682287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s4_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2136033813/5000000000 : ℝ)*x 0 + (403256179/1000000000 : ℝ)*x 1 + (4523599301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136033813/5000000000 : ℝ)^4511 ≤ (33279018255561/100000000000000 : ℝ)^3487 := by
    have hnat : (2136033813 : ℕ)^4511*100000000000000^3487 ≤ 33279018255561^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136033813 5000000000 33279018255561 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403256179/1000000000 : ℝ)^4511 ≤ (30885532880683/100000000000000 : ℝ)^3487 := by
    have hnat : (403256179 : ℕ)^4511*100000000000000^3487 ≤ 30885532880683^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403256179 1000000000 30885532880683 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523599301/10000000000 : ℝ)^4511 ≤ (35835448848861/100000000000000 : ℝ)^3487 := by
    have hnat : (4523599301 : ℕ)^4511*100000000000000^3487 ≤ 35835448848861^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523599301 10000000000 35835448848861 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136033813/5000000000 : ℝ), (403256179/1000000000 : ℝ), (4523599301/10000000000 : ℝ)] ![(33279018255561/100000000000000 : ℝ), (30885532880683/100000000000000 : ℝ), (35835448848861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136033813/5000000000 : ℝ)|^4511 ≤ (33279018255561/100000000000000 : ℝ)^3487
        have hw : |(2136033813/5000000000 : ℝ)|=(2136033813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403256179/1000000000 : ℝ)|^4511 ≤ (30885532880683/100000000000000 : ℝ)^3487
        have hw : |(403256179/1000000000 : ℝ)|=(403256179/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523599301/10000000000 : ℝ)|^4511 ≤ (35835448848861/100000000000000 : ℝ)^3487
        have hw : |(4523599301/10000000000 : ℝ)|=(4523599301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s4_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875394607/10000000000 : ℝ)*x 0 + (163066233/312500000 : ℝ)*x 1 + (2716589583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875394607/10000000000 : ℝ)^4511 ≤ (11471691888093/100000000000000 : ℝ)^3487 := by
    have hnat : (1875394607 : ℕ)^4511*100000000000000^3487 ≤ 11471691888093^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875394607 10000000000 11471691888093 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163066233/312500000 : ℝ)^4511 ≤ (43108068981471/100000000000000 : ℝ)^3487 := by
    have hnat : (163066233 : ℕ)^4511*100000000000000^3487 ≤ 43108068981471^3487*312500000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163066233 312500000 43108068981471 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716589583/5000000000 : ℝ)^4511 ≤ (45420239113763/100000000000000 : ℝ)^3487 := by
    have hnat : (2716589583 : ℕ)^4511*100000000000000^3487 ≤ 45420239113763^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716589583 5000000000 45420239113763 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875394607/10000000000 : ℝ), (163066233/312500000 : ℝ), (2716589583/5000000000 : ℝ)] ![(11471691888093/100000000000000 : ℝ), (43108068981471/100000000000000 : ℝ), (45420239113763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875394607/10000000000 : ℝ)|^4511 ≤ (11471691888093/100000000000000 : ℝ)^3487
        have hw : |(-1875394607/10000000000 : ℝ)|=(1875394607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163066233/312500000 : ℝ)|^4511 ≤ (43108068981471/100000000000000 : ℝ)^3487
        have hw : |(163066233/312500000 : ℝ)|=(163066233/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716589583/5000000000 : ℝ)|^4511 ≤ (45420239113763/100000000000000 : ℝ)^3487
        have hw : |(2716589583/5000000000 : ℝ)|=(2716589583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s4_5 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529497457/1000000000 : ℝ)*x 0 + (-177050133/1000000000 : ℝ)*x 1 + (5433179219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529497457/1000000000 : ℝ)^4511 ≤ (43931207956453/100000000000000 : ℝ)^3487 := by
    have hnat : (529497457 : ℕ)^4511*100000000000000^3487 ≤ 43931207956453^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529497457 1000000000 43931207956453 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177050133/1000000000 : ℝ)^4511 ≤ (10648552337473/100000000000000 : ℝ)^3487 := by
    have hnat : (177050133 : ℕ)^4511*100000000000000^3487 ≤ 10648552337473^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177050133 1000000000 10648552337473 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433179219/10000000000 : ℝ)^4511 ≤ (9084047937389/20000000000000 : ℝ)^3487 := by
    have hnat : (5433179219 : ℕ)^4511*20000000000000^3487 ≤ 9084047937389^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433179219 10000000000 9084047937389 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529497457/1000000000 : ℝ), (-177050133/1000000000 : ℝ), (5433179219/10000000000 : ℝ)] ![(43931207956453/100000000000000 : ℝ), (10648552337473/100000000000000 : ℝ), (9084047937389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529497457/1000000000 : ℝ)|^4511 ≤ (43931207956453/100000000000000 : ℝ)^3487
        have hw : |(529497457/1000000000 : ℝ)|=(529497457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177050133/1000000000 : ℝ)|^4511 ≤ (10648552337473/100000000000000 : ℝ)^3487
        have hw : |(-177050133/1000000000 : ℝ)|=(177050133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433179219/10000000000 : ℝ)|^4511 ≤ (9084047937389/20000000000000 : ℝ)^3487
        have hw : |(5433179219/10000000000 : ℝ)|=(5433179219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s4_6 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294974783/10000000000 : ℝ)*x 0 + (5433179053/10000000000 : ℝ)*x 1 + (-442625317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294974783/10000000000 : ℝ)^4511 ≤ (43931210242629/100000000000000 : ℝ)^3487 := by
    have hnat : (5294974783 : ℕ)^4511*100000000000000^3487 ≤ 43931210242629^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294974783 10000000000 43931210242629 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433179053/10000000000 : ℝ)^4511 ≤ (45420237891697/100000000000000 : ℝ)^3487 := by
    have hnat : (5433179053 : ℕ)^4511*100000000000000^3487 ≤ 45420237891697^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433179053 10000000000 45420237891697 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442625317/2500000000 : ℝ)^4511 ≤ (10648551855073/100000000000000 : ℝ)^3487 := by
    have hnat : (442625317 : ℕ)^4511*100000000000000^3487 ≤ 10648551855073^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442625317 2500000000 10648551855073 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294974783/10000000000 : ℝ), (5433179053/10000000000 : ℝ), (-442625317/2500000000 : ℝ)] ![(43931210242629/100000000000000 : ℝ), (45420237891697/100000000000000 : ℝ), (10648551855073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294974783/10000000000 : ℝ)|^4511 ≤ (43931210242629/100000000000000 : ℝ)^3487
        have hw : |(5294974783/10000000000 : ℝ)|=(5294974783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433179053/10000000000 : ℝ)|^4511 ≤ (45420237891697/100000000000000 : ℝ)^3487
        have hw : |(5433179053/10000000000 : ℝ)|=(5433179053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442625317/2500000000 : ℝ)|^4511 ≤ (10648551855073/100000000000000 : ℝ)^3487
        have hw : |(-442625317/2500000000 : ℝ)|=(442625317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s4_7 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4272133013/10000000000 : ℝ)*x 0 + (2260532433/5000000000 : ℝ)*x 1 + (4035116247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272133013/10000000000 : ℝ)^4511 ≤ (33279677195233/100000000000000 : ℝ)^3487 := by
    have hnat : (4272133013 : ℕ)^4511*100000000000000^3487 ≤ 33279677195233^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272133013 10000000000 33279677195233 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260532433/5000000000 : ℝ)^4511 ≤ (35809477469021/100000000000000 : ℝ)^3487 := by
    have hnat : (2260532433 : ℕ)^4511*100000000000000^3487 ≤ 35809477469021^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260532433 5000000000 35809477469021 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035116247/10000000000 : ℝ)^4511 ≤ (30910845315993/100000000000000 : ℝ)^3487 := by
    have hnat : (4035116247 : ℕ)^4511*100000000000000^3487 ≤ 30910845315993^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035116247 10000000000 30910845315993 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272133013/10000000000 : ℝ), (2260532433/5000000000 : ℝ), (4035116247/10000000000 : ℝ)] ![(33279677195233/100000000000000 : ℝ), (35809477469021/100000000000000 : ℝ), (30910845315993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272133013/10000000000 : ℝ)|^4511 ≤ (33279677195233/100000000000000 : ℝ)^3487
        have hw : |(4272133013/10000000000 : ℝ)|=(4272133013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2260532433/5000000000 : ℝ)|^4511 ≤ (35809477469021/100000000000000 : ℝ)^3487
        have hw : |(2260532433/5000000000 : ℝ)|=(2260532433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035116247/10000000000 : ℝ)|^4511 ≤ (30910845315993/100000000000000 : ℝ)^3487
        have hw : |(4035116247/10000000000 : ℝ)|=(4035116247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15553/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1361/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15553/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1083/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15553/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1083/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15553/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1083/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15553/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1083/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15553/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1083/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15553/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1083/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1083/10000 : ℝ) ^ (4509/1024 : ℝ) ≤ (175392046538959/3125000000000000000 : ℝ) := by
    have hpowers : (1083/10000 : ℝ)^4509 ≤ (175392046538959/3125000000000000000 : ℝ)^1024 := by
      have hnat : (1083 : ℕ)^4509*3125000000000000000^1024 ≤ 175392046538959^1024*10000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1083 10000 175392046538959 3125000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1083/10000 : ℝ)) (X := (175392046538959/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15553/100000 : ℝ) ^ (4509/1024 : ℝ) ≤ (27624786312566381/100000000000000000000 : ℝ) := by
    have hpowers : (15553/100000 : ℝ)^4509 ≤ (27624786312566381/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15553 : ℕ)^4509*100000000000000000000^1024 ≤ 27624786312566381^1024*100000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15553 100000 27624786312566381 100000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15553/100000 : ℝ)) (X := (27624786312566381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562675392046538959/1562500000000000000 : ℝ) ≤ (10000254912277049/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (1562675392046538959/1562500000000000000 : ℝ)^1024 ≤ (10000254912277049/10000000000000000 : ℝ)^4509 := by
      have hnat : (1562675392046538959 : ℕ)^1024*10000000000000000^4509 ≤ 10000254912277049^4509*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562675392046538959 1562500000000000000 10000254912277049 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000254912277049/10000000000000000 : ℝ)) (X := (1562675392046538959/1562500000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033237331801813069/100000000000000000000 : ℝ) ≤ (10000754727367029/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (100033237331801813069/100000000000000000000 : ℝ)^1024 ≤ (10000754727367029/10000000000000000 : ℝ)^4509 := by
      have hnat : (100033237331801813069 : ℕ)^1024*10000000000000000^4509 ≤ 10000754727367029^4509*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033237331801813069 100000000000000000000 10000754727367029 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000754727367029/10000000000000000 : ℝ)) (X := (100033237331801813069/100000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027624786312566381/50000000000000000000 : ℝ) ≤ (10001254542457009/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (50027624786312566381/50000000000000000000 : ℝ)^1024 ≤ (10001254542457009/10000000000000000 : ℝ)^4509 := by
      have hnat : (50027624786312566381 : ℕ)^1024*10000000000000000^4509 ≤ 10001254542457009^4509*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027624786312566381 50000000000000000000 10001254542457009 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001254542457009/10000000000000000 : ℝ)) (X := (50027624786312566381/50000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(175392046538959/3125000000000000000 : ℝ) ≤ ((47220377955835535627/47230000000000000000 : ℝ)+2*(24990754499/23615000000000 : ℝ)*(1083/10000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (47220377955835535627/47230000000000000000 : ℝ)+2*(24990754499/23615000000000 : ℝ)*(1083/10000 : ℝ)=(10000254912277049/10000000000000000 : ℝ) by norm_num, show 1+2*(175392046538959/3125000000000000000 : ℝ)=(1562675392046538959/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27624786312566381/100000000000000000000 : ℝ)+(175392046538959/3125000000000000000 : ℝ) ≤ ((47220377955835535627/47230000000000000000 : ℝ)+(24990754499/23615000000000 : ℝ)*((15553/100000 : ℝ)+(1083/10000 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (47220377955835535627/47230000000000000000 : ℝ)+(24990754499/23615000000000 : ℝ)*((15553/100000 : ℝ)+(1083/10000 : ℝ))=(10000754727367029/10000000000000000 : ℝ) by norm_num, show 1+(27624786312566381/100000000000000000000 : ℝ)+(175392046538959/3125000000000000000 : ℝ)=(100033237331801813069/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27624786312566381/100000000000000000000 : ℝ) ≤ ((47220377955835535627/47230000000000000000 : ℝ)+2*(24990754499/23615000000000 : ℝ)*(15553/100000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (47220377955835535627/47230000000000000000 : ℝ)+2*(24990754499/23615000000000 : ℝ)*(15553/100000 : ℝ)=(10001254542457009/10000000000000000 : ℝ) by norm_num, show 1+2*(27624786312566381/100000000000000000000 : ℝ)=(50027624786312566381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47220377955835535627/47230000000000000000 : ℝ)*(X 1 0+X 2 0)+(24990754499/23615000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (15553/100000 : ℝ)) (c := (47220377955835535627/47230000000000000000 : ℝ)) (alpha := (24990754499/23615000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47220377955835535627/47230000000000000000 : ℝ)*(X 0 1+X 2 1)+(24990754499/23615000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (15553/100000 : ℝ)) (c := (47220377955835535627/47230000000000000000 : ℝ)) (alpha := (24990754499/23615000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47220377955835535627/47230000000000000000 : ℝ)*(X 0 2+X 1 2)+(24990754499/23615000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (15553/100000 : ℝ)) (c := (47220377955835535627/47230000000000000000 : ℝ)) (alpha := (24990754499/23615000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1875365821/10000000000 : ℝ)*X 0 0+(543430771/1000000000 : ℝ)*X 0 1+(1304249673/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337994581/2500000000 : ℝ)*X 1 0+(-397336607/2000000000 : ℝ)*X 1 1+(2608498713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070395537/2000000000 : ℝ)*X 2 0+(5216998633/10000000000 : ℝ)*X 2 1+(-1986682287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2136033813/5000000000 : ℝ)*X 0 0+(403256179/1000000000 : ℝ)*X 0 1+(4523599301/10000000000 : ℝ)*X 0 2+(2136033813/5000000000 : ℝ)*X 1 0+(403256179/1000000000 : ℝ)*X 1 1+(4523599301/10000000000 : ℝ)*X 1 2+(2136033813/5000000000 : ℝ)*X 2 0+(403256179/1000000000 : ℝ)*X 2 1+(4523599301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1875394607/10000000000 : ℝ)*X 0 0+(163066233/312500000 : ℝ)*X 0 1+(2716589583/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529497457/1000000000 : ℝ)*X 1 0+(-177050133/1000000000 : ℝ)*X 1 1+(5433179219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294974783/10000000000 : ℝ)*X 2 0+(5433179053/10000000000 : ℝ)*X 2 1+(-442625317/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4272133013/10000000000 : ℝ)*X 0 0+(2260532433/5000000000 : ℝ)*X 0 1+(4035116247/10000000000 : ℝ)*X 0 2+(4272133013/10000000000 : ℝ)*X 1 0+(2260532433/5000000000 : ℝ)*X 1 1+(4035116247/10000000000 : ℝ)*X 1 2+(4272133013/10000000000 : ℝ)*X 2 0+(2260532433/5000000000 : ℝ)*X 2 1+(4035116247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9103465484998068455483513679/1180750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (609594031/25000000000000 : ℝ)*(base19) + (1810985901/100000000000000 : ℝ)*(base23) + (21695919/12500000000000 : ℝ)*(upper3) + (20862607/50000000000000 : ℝ)*(upper4) + (371820913/50000000000000 : ℝ)*(upper5) + (3319153423788241/100000000000000 : ℝ)*(major0) + (3319153423788241/100000000000000 : ℝ)*(major1) + (3319153423788241/100000000000000 : ℝ)*(major2) + (4601746130771029/100000000000000 : ℝ)*(sp0) + (4601762663817453/100000000000000 : ℝ)*(sp1) + (4601763291207677/100000000000000 : ℝ)*(sp2) + (407305276456441/20000000000000 : ℝ)*(sp3) + (4742855637/25000000000000 : ℝ)*(sp4) + (15106103993/100000000000000 : ℝ)*(sp7) + (1018270744193099/50000000000000 : ℝ)*(f.failure) + (2300882551096789/50000000000000 : ℝ)*(f.sum) + (6067024628013/2361500000000000000000000000 : ℝ)*base66 + (76637326591559162107/4723000000000000000000000000000000 : ℝ)*base67 + (79503443029501162107/4723000000000000000000000000000000 : ℝ)*base69 + (30505326585224162107/4723000000000000000000000000000000 : ℝ)*base71 + (7792333451823/4723000000000000000000000000 : ℝ)*base74 + (11244972977564837893/4723000000000000000000000000000000 : ℝ)*base76 + (47244588035745162107/4723000000000000000000000000000000 : ℝ)*base77 + (53150423500010162107/4723000000000000000000000000000000 : ℝ)*base79 + (3496548459487/944600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (15061793/5000000000000000000000 : ℝ)*base89 + (15061793/5000000000000000000000 : ℝ)*base91 + (15061793/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9177100115180454304053023943/1180750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (580440971/50000000000000 : ℝ)*(base19) + (179463693/12500000000000 : ℝ)*(base23) + (169609647/100000000000000 : ℝ)*(upper3) + (28101341/100000000000000 : ℝ)*(lower4) + (149916727/100000000000000 : ℝ)*(upper5) + (1676925763526899/50000000000000 : ℝ)*(major0) + (1676925763526899/50000000000000 : ℝ)*(major1) + (1676925763526899/50000000000000 : ℝ)*(major2) + (17817811813/100000000000000 : ℝ)*(sp1) + (21041939039/100000000000000 : ℝ)*(sp2) + (581233937791943/12500000000000 : ℝ)*(sp4) + (1162463130910447/25000000000000 : ℝ)*(sp5) + (58123112808587/1250000000000 : ℝ)*(sp6) + (514457823174147/25000000000000 : ℝ)*(sp7) + (514457823174147/25000000000000 : ℝ)*(f.failure) + (581233937791943/12500000000000 : ℝ)*(f.sum) + (1567578289279/236150000000000000000000000 : ℝ)*base65 + (17145386999661330673/2361500000000000000000000000000000 : ℝ)*base67 + (4228642586779330673/2361500000000000000000000000000000 : ℝ)*base69 + (14993562355405330673/2361500000000000000000000000000000 : ℝ)*base71 + (20335837643309/4723000000000000000000000000 : ℝ)*base73 + (36975750575710330673/2361500000000000000000000000000000 : ℝ)*base75 + (19738283850390830673/2361500000000000000000000000000000 : ℝ)*base77 + (37218518374826830673/2361500000000000000000000000000000 : ℝ)*base79 + (14741486414159/4723000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (27135671/2500000000000000000000 : ℝ)*base90 + (27135671/2500000000000000000000 : ℝ)*base92 + (27135671/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1507_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15553/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1507_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1507_s5_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875422751/10000000000 : ℝ)*x 0 + (5433931521/10000000000 : ℝ)*x 1 + (5217337253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875422751/10000000000 : ℝ)^4511 ≤ (2294382919901/20000000000000 : ℝ)^3487 := by
    have hnat : (1875422751 : ℕ)^4511*20000000000000^3487 ≤ 2294382919901^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875422751 10000000000 2294382919901 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433931521/10000000000 : ℝ)^4511 ≤ (11357093951599/25000000000000 : ℝ)^3487 := by
    have hnat : (5433931521 : ℕ)^4511*25000000000000^3487 ≤ 11357093951599^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433931521 10000000000 11357093951599 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217337253/10000000000 : ℝ)^4511 ≤ (21549854788397/50000000000000 : ℝ)^3487 := by
    have hnat : (5217337253 : ℕ)^4511*50000000000000^3487 ≤ 21549854788397^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217337253 10000000000 21549854788397 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875422751/10000000000 : ℝ), (5433931521/10000000000 : ℝ), (5217337253/10000000000 : ℝ)] ![(2294382919901/20000000000000 : ℝ), (11357093951599/25000000000000 : ℝ), (21549854788397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875422751/10000000000 : ℝ)|^4511 ≤ (2294382919901/20000000000000 : ℝ)^3487
        have hw : |(-1875422751/10000000000 : ℝ)|=(1875422751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433931521/10000000000 : ℝ)|^4511 ≤ (11357093951599/25000000000000 : ℝ)^3487
        have hw : |(5433931521/10000000000 : ℝ)|=(5433931521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217337253/10000000000 : ℝ)|^4511 ≤ (21549854788397/50000000000000 : ℝ)^3487
        have hw : |(5217337253/10000000000 : ℝ)|=(5217337253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s5_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351879337/10000000000 : ℝ)*x 0 + (-496591061/2500000000 : ℝ)*x 1 + (130433431/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351879337/10000000000 : ℝ)^4511 ≤ (44542940861781/100000000000000 : ℝ)^3487 := by
    have hnat : (5351879337 : ℕ)^4511*100000000000000^3487 ≤ 44542940861781^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351879337 10000000000 44542940861781 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496591061/2500000000 : ℝ)^4511 ≤ (6178674843541/50000000000000 : ℝ)^3487 := by
    have hnat : (496591061 : ℕ)^4511*50000000000000^3487 ≤ 6178674843541^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496591061 2500000000 6178674843541 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130433431/250000000 : ℝ)^4511 ≤ (21549854718933/50000000000000 : ℝ)^3487 := by
    have hnat : (130433431 : ℕ)^4511*50000000000000^3487 ≤ 21549854718933^3487*250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130433431 250000000 21549854718933 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351879337/10000000000 : ℝ), (-496591061/2500000000 : ℝ), (130433431/250000000 : ℝ)] ![(44542940861781/100000000000000 : ℝ), (6178674843541/50000000000000 : ℝ), (21549854718933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351879337/10000000000 : ℝ)|^4511 ≤ (44542940861781/100000000000000 : ℝ)^3487
        have hw : |(5351879337/10000000000 : ℝ)|=(5351879337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496591061/2500000000 : ℝ)|^4511 ≤ (6178674843541/50000000000000 : ℝ)^3487
        have hw : |(-496591061/2500000000 : ℝ)|=(496591061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130433431/250000000 : ℝ)|^4511 ≤ (21549854718933/50000000000000 : ℝ)^3487
        have hw : |(130433431/250000000 : ℝ)|=(130433431/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s5_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351879331/10000000000 : ℝ)*x 0 + (5217337253/10000000000 : ℝ)*x 1 + (-397272847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351879331/10000000000 : ℝ)^4511 ≤ (44542940797179/100000000000000 : ℝ)^3487 := by
    have hnat : (5351879331 : ℕ)^4511*100000000000000^3487 ≤ 44542940797179^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351879331 10000000000 44542940797179 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217337253/10000000000 : ℝ)^4511 ≤ (21549854788397/50000000000000 : ℝ)^3487 := by
    have hnat : (5217337253 : ℕ)^4511*50000000000000^3487 ≤ 21549854788397^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217337253 10000000000 21549854788397 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397272847/2000000000 : ℝ)^4511 ≤ (247146992293/2000000000000 : ℝ)^3487 := by
    have hnat : (397272847 : ℕ)^4511*2000000000000^3487 ≤ 247146992293^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397272847 2000000000 247146992293 2000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351879331/10000000000 : ℝ), (5217337253/10000000000 : ℝ), (-397272847/2000000000 : ℝ)] ![(44542940797179/100000000000000 : ℝ), (21549854788397/50000000000000 : ℝ), (247146992293/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351879331/10000000000 : ℝ)|^4511 ≤ (44542940797179/100000000000000 : ℝ)^3487
        have hw : |(5351879331/10000000000 : ℝ)|=(5351879331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217337253/10000000000 : ℝ)|^4511 ≤ (21549854788397/50000000000000 : ℝ)^3487
        have hw : |(5217337253/10000000000 : ℝ)|=(5217337253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397272847/2000000000 : ℝ)|^4511 ≤ (247146992293/2000000000000 : ℝ)^3487
        have hw : |(-397272847/2000000000 : ℝ)|=(397272847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s5_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2136050943/5000000000 : ℝ)*x 0 + (4033369067/10000000000 : ℝ)*x 1 + (4522785077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136050943/5000000000 : ℝ)^4511 ≤ (8319840877871/25000000000000 : ℝ)^3487 := by
    have hnat : (2136050943 : ℕ)^4511*25000000000000^3487 ≤ 8319840877871^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136050943 5000000000 8319840877871 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4033369067/10000000000 : ℝ)^4511 ≤ (6178706356227/20000000000000 : ℝ)^3487 := by
    have hnat : (4033369067 : ℕ)^4511*20000000000000^3487 ≤ 6178706356227^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033369067 10000000000 6178706356227 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522785077/10000000000 : ℝ)^4511 ≤ (2239194043777/6250000000000 : ℝ)^3487 := by
    have hnat : (4522785077 : ℕ)^4511*6250000000000^3487 ≤ 2239194043777^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522785077 10000000000 2239194043777 6250000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136050943/5000000000 : ℝ), (4033369067/10000000000 : ℝ), (4522785077/10000000000 : ℝ)] ![(8319840877871/25000000000000 : ℝ), (6178706356227/20000000000000 : ℝ), (2239194043777/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136050943/5000000000 : ℝ)|^4511 ≤ (8319840877871/25000000000000 : ℝ)^3487
        have hw : |(2136050943/5000000000 : ℝ)|=(2136050943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4033369067/10000000000 : ℝ)|^4511 ≤ (6178706356227/20000000000000 : ℝ)^3487
        have hw : |(4033369067/10000000000 : ℝ)|=(4033369067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522785077/10000000000 : ℝ)|^4511 ≤ (2239194043777/6250000000000 : ℝ)^3487
        have hw : |(4522785077/10000000000 : ℝ)|=(4522785077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s5_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-937726097/5000000000 : ℝ)*x 0 + (2609225717/5000000000 : ℝ)*x 1 + (2716404479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (937726097/5000000000 : ℝ)^4511 ≤ (286803689783/2500000000000 : ℝ)^3487 := by
    have hnat : (937726097 : ℕ)^4511*2500000000000^3487 ≤ 286803689783^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937726097 5000000000 286803689783 2500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609225717/5000000000 : ℝ)^4511 ≤ (10777904235527/25000000000000 : ℝ)^3487 := by
    have hnat : (2609225717 : ℕ)^4511*25000000000000^3487 ≤ 10777904235527^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609225717 5000000000 10777904235527 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716404479/5000000000 : ℝ)^4511 ≤ (11354058862209/25000000000000 : ℝ)^3487 := by
    have hnat : (2716404479 : ℕ)^4511*25000000000000^3487 ≤ 11354058862209^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716404479 5000000000 11354058862209 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-937726097/5000000000 : ℝ), (2609225717/5000000000 : ℝ), (2716404479/5000000000 : ℝ)] ![(286803689783/2500000000000 : ℝ), (10777904235527/25000000000000 : ℝ), (11354058862209/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-937726097/5000000000 : ℝ)|^4511 ≤ (286803689783/2500000000000 : ℝ)^3487
        have hw : |(-937726097/5000000000 : ℝ)|=(937726097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609225717/5000000000 : ℝ)|^4511 ≤ (10777904235527/25000000000000 : ℝ)^3487
        have hw : |(2609225717/5000000000 : ℝ)|=(2609225717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716404479/5000000000 : ℝ)|^4511 ≤ (11354058862209/25000000000000 : ℝ)^3487
        have hw : |(2716404479/5000000000 : ℝ)|=(2716404479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s5_5 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323766003/2500000000 : ℝ)*x 0 + (-5534039/31250000 : ℝ)*x 1 + (5432809027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323766003/2500000000 : ℝ)^4511 ≤ (43932167959751/100000000000000 : ℝ)^3487 := by
    have hnat : (1323766003 : ℕ)^4511*100000000000000^3487 ≤ 43932167959751^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323766003 2500000000 43932167959751 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5534039/31250000 : ℝ)^4511 ≤ (10651595832621/100000000000000 : ℝ)^3487 := by
    have hnat : (5534039 : ℕ)^4511*100000000000000^3487 ≤ 10651595832621^3487*31250000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534039 31250000 10651595832621 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432809027/10000000000 : ℝ)^4511 ≤ (45416236195039/100000000000000 : ℝ)^3487 := by
    have hnat : (5432809027 : ℕ)^4511*100000000000000^3487 ≤ 45416236195039^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432809027 10000000000 45416236195039 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323766003/2500000000 : ℝ), (-5534039/31250000 : ℝ), (5432809027/10000000000 : ℝ)] ![(43932167959751/100000000000000 : ℝ), (10651595832621/100000000000000 : ℝ), (45416236195039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323766003/2500000000 : ℝ)|^4511 ≤ (43932167959751/100000000000000 : ℝ)^3487
        have hw : |(1323766003/2500000000 : ℝ)|=(1323766003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5534039/31250000 : ℝ)|^4511 ≤ (10651595832621/100000000000000 : ℝ)^3487
        have hw : |(-5534039/31250000 : ℝ)|=(5534039/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432809027/10000000000 : ℝ)|^4511 ≤ (45416236195039/100000000000000 : ℝ)^3487
        have hw : |(5432809027/10000000000 : ℝ)|=(5432809027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s5_6 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295064197/10000000000 : ℝ)*x 0 + (1358202261/2500000000 : ℝ)*x 1 + (-1770892201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295064197/10000000000 : ℝ)^4511 ≤ (43932169945407/100000000000000 : ℝ)^3487 := by
    have hnat : (5295064197 : ℕ)^4511*100000000000000^3487 ≤ 43932169945407^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295064197 10000000000 43932169945407 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358202261/2500000000 : ℝ)^4511 ≤ (22708118189443/50000000000000 : ℝ)^3487 := by
    have hnat : (1358202261 : ℕ)^4511*50000000000000^3487 ≤ 22708118189443^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358202261 2500000000 22708118189443 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1770892201/10000000000 : ℝ)^4511 ≤ (10651593661683/100000000000000 : ℝ)^3487 := by
    have hnat : (1770892201 : ℕ)^4511*100000000000000^3487 ≤ 10651593661683^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770892201 10000000000 10651593661683 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295064197/10000000000 : ℝ), (1358202261/2500000000 : ℝ), (-1770892201/10000000000 : ℝ)] ![(43932169945407/100000000000000 : ℝ), (22708118189443/50000000000000 : ℝ), (10651593661683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295064197/10000000000 : ℝ)|^4511 ≤ (43932169945407/100000000000000 : ℝ)^3487
        have hw : |(5295064197/10000000000 : ℝ)|=(5295064197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358202261/2500000000 : ℝ)|^4511 ≤ (22708118189443/50000000000000 : ℝ)^3487
        have hw : |(1358202261/2500000000 : ℝ)|=(1358202261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1770892201/10000000000 : ℝ)|^4511 ≤ (10651593661683/100000000000000 : ℝ)^3487
        have hw : |(-1770892201/10000000000 : ℝ)|=(1770892201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s5_7 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4272168087/10000000000 : ℝ)*x 0 + (452026707/1000000000 : ℝ)*x 1 + (4035905423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272168087/10000000000 : ℝ)^4511 ≤ (33280030655857/100000000000000 : ℝ)^3487 := by
    have hnat : (4272168087 : ℕ)^4511*100000000000000^3487 ≤ 33280030655857^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272168087 10000000000 33280030655857 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452026707/1000000000 : ℝ)^4511 ≤ (1790065150777/5000000000000 : ℝ)^3487 := by
    have hnat : (452026707 : ℕ)^4511*5000000000000^3487 ≤ 1790065150777^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452026707 1000000000 1790065150777 5000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035905423/10000000000 : ℝ)^4511 ≤ (386483328897/1250000000000 : ℝ)^3487 := by
    have hnat : (4035905423 : ℕ)^4511*1250000000000^3487 ≤ 386483328897^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035905423 10000000000 386483328897 1250000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272168087/10000000000 : ℝ), (452026707/1000000000 : ℝ), (4035905423/10000000000 : ℝ)] ![(33280030655857/100000000000000 : ℝ), (1790065150777/5000000000000 : ℝ), (386483328897/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272168087/10000000000 : ℝ)|^4511 ≤ (33280030655857/100000000000000 : ℝ)^3487
        have hw : |(4272168087/10000000000 : ℝ)|=(4272168087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(452026707/1000000000 : ℝ)|^4511 ≤ (1790065150777/5000000000000 : ℝ)^3487
        have hw : |(452026707/1000000000 : ℝ)|=(452026707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035905423/10000000000 : ℝ)|^4511 ≤ (386483328897/1250000000000 : ℝ)^3487
        have hw : |(4035905423/10000000000 : ℝ)|=(4035905423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (681/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1361/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1361/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1361/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1361/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1361/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1361/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1361/12500 : ℝ) ^ (4509/1024 : ℝ) ≤ (2873055825845009/50000000000000000000 : ℝ) := by
    have hpowers : (1361/12500 : ℝ)^4509 ≤ (2873055825845009/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1361 : ℕ)^4509*50000000000000000000^1024 ≤ 2873055825845009^1024*12500^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1361 12500 2873055825845009 50000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1361/12500 : ℝ)) (X := (2873055825845009/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4509/1024 : ℝ) ≤ (6783861369902419/25000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4509 ≤ (6783861369902419/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4509*25000000000000000000^1024 ≤ 6783861369902419^1024*10000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 6783861369902419 25000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (6783861369902419/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002873055825845009/25000000000000000000 : ℝ) ≤ (10000260978355747/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (25002873055825845009/25000000000000000000 : ℝ)^1024 ≤ (10000260978355747/10000000000000000 : ℝ)^4509 := by
      have hnat : (25002873055825845009 : ℕ)^1024*10000000000000000^4509 ≤ 10000260978355747^4509*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002873055825845009 25000000000000000000 10000260978355747 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000260978355747/10000000000000000 : ℝ)) (X := (25002873055825845009/25000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016440778565649847/50000000000000000000 : ℝ) ≤ (625046665608751/625000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (50016440778565649847/50000000000000000000 : ℝ)^1024 ≤ (625046665608751/625000000000000 : ℝ)^4509 := by
      have hnat : (50016440778565649847 : ℕ)^1024*625000000000000^4509 ≤ 625046665608751^4509*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016440778565649847 50000000000000000000 625046665608751 625000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625046665608751/625000000000000 : ℝ)) (X := (50016440778565649847/50000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506783861369902419/12500000000000000000 : ℝ) ≤ (2000246464224857/2000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (12506783861369902419/12500000000000000000 : ℝ)^1024 ≤ (2000246464224857/2000000000000000 : ℝ)^4509 := by
      have hnat : (12506783861369902419 : ℕ)^1024*2000000000000000^4509 ≤ 2000246464224857^4509*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506783861369902419 12500000000000000000 2000246464224857 2000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000246464224857/2000000000000000 : ℝ)) (X := (12506783861369902419/12500000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2873055825845009/50000000000000000000 : ℝ) ≤ ((306737500282195373/306800000000000000 : ℝ)+2*(161890461423/153400000000000 : ℝ)*(1361/12500 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (306737500282195373/306800000000000000 : ℝ)+2*(161890461423/153400000000000 : ℝ)*(1361/12500 : ℝ)=(10000260978355747/10000000000000000 : ℝ) by norm_num, show 1+2*(2873055825845009/50000000000000000000 : ℝ)=(25002873055825845009/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6783861369902419/25000000000000000000 : ℝ)+(2873055825845009/50000000000000000000 : ℝ) ≤ ((306737500282195373/306800000000000000 : ℝ)+(161890461423/153400000000000 : ℝ)*((1549/10000 : ℝ)+(1361/12500 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (306737500282195373/306800000000000000 : ℝ)+(161890461423/153400000000000 : ℝ)*((1549/10000 : ℝ)+(1361/12500 : ℝ))=(625046665608751/625000000000000 : ℝ) by norm_num, show 1+(6783861369902419/25000000000000000000 : ℝ)+(2873055825845009/50000000000000000000 : ℝ)=(50016440778565649847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6783861369902419/25000000000000000000 : ℝ) ≤ ((306737500282195373/306800000000000000 : ℝ)+2*(161890461423/153400000000000 : ℝ)*(1549/10000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (306737500282195373/306800000000000000 : ℝ)+2*(161890461423/153400000000000 : ℝ)*(1549/10000 : ℝ)=(2000246464224857/2000000000000000 : ℝ) by norm_num, show 1+2*(6783861369902419/25000000000000000000 : ℝ)=(12506783861369902419/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (306737500282195373/306800000000000000 : ℝ)*(X 1 0+X 2 0)+(161890461423/153400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (306737500282195373/306800000000000000 : ℝ)) (alpha := (161890461423/153400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (306737500282195373/306800000000000000 : ℝ)*(X 0 1+X 2 1)+(161890461423/153400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (306737500282195373/306800000000000000 : ℝ)) (alpha := (161890461423/153400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (306737500282195373/306800000000000000 : ℝ)*(X 0 2+X 1 2)+(161890461423/153400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (306737500282195373/306800000000000000 : ℝ)) (alpha := (161890461423/153400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1875422751/10000000000 : ℝ)*X 0 0+(5433931521/10000000000 : ℝ)*X 0 1+(5217337253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351879337/10000000000 : ℝ)*X 1 0+(-496591061/2500000000 : ℝ)*X 1 1+(130433431/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351879331/10000000000 : ℝ)*X 2 0+(5217337253/10000000000 : ℝ)*X 2 1+(-397272847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2136050943/5000000000 : ℝ)*X 0 0+(4033369067/10000000000 : ℝ)*X 0 1+(4522785077/10000000000 : ℝ)*X 0 2+(2136050943/5000000000 : ℝ)*X 1 0+(4033369067/10000000000 : ℝ)*X 1 1+(4522785077/10000000000 : ℝ)*X 1 2+(2136050943/5000000000 : ℝ)*X 2 0+(4033369067/10000000000 : ℝ)*X 2 1+(4522785077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-937726097/5000000000 : ℝ)*X 0 0+(2609225717/5000000000 : ℝ)*X 0 1+(2716404479/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323766003/2500000000 : ℝ)*X 1 0+(-5534039/31250000 : ℝ)*X 1 1+(5432809027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295064197/10000000000 : ℝ)*X 2 0+(1358202261/2500000000 : ℝ)*X 2 1+(-1770892201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4272168087/10000000000 : ℝ)*X 0 0+(452026707/1000000000 : ℝ)*X 0 1+(4035905423/10000000000 : ℝ)*X 0 2+(4272168087/10000000000 : ℝ)*X 1 0+(452026707/1000000000 : ℝ)*X 1 1+(4035905423/10000000000 : ℝ)*X 1 2+(4272168087/10000000000 : ℝ)*X 2 0+(452026707/1000000000 : ℝ)*X 2 1+(4035905423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17175931724869357610968113/7670000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399770029/100000000000000 : ℝ)*(base19) + (366248297/100000000000000 : ℝ)*(base23) + (15170263/100000000000000 : ℝ)*(lower2) + (50128379/100000000000000 : ℝ)*(upper3) + (37251861/100000000000000 : ℝ)*(upper5) + (1665049291837709/50000000000000 : ℝ)*(major0) + (1665049291837709/50000000000000 : ℝ)*(major1) + (1665049291837709/50000000000000 : ℝ)*(major2) + (923386737214441/20000000000000 : ℝ)*(sp0) + (288558722168417/6250000000000 : ℝ)*(sp1) + (923387917643281/20000000000000 : ℝ)*(sp2) + (2043254201499367/100000000000000 : ℝ)*(sp3) + (391774531/6250000000000 : ℝ)*(sp4) + (2349393/80000000000 : ℝ)*(sp7) + (2043257138240617/100000000000000 : ℝ)*(f.failure) + (4616939954464701/100000000000000 : ℝ)*(f.sum) + (105670629713/958750000000000000000000000 : ℝ)*base65 + (137669663417185543/15340000000000000000000000000000 : ℝ)*base68 + (67796667277745543/15340000000000000000000000000000 : ℝ)*base70 + (145820667801305543/15340000000000000000000000000000 : ℝ)*base72 + (1246919163383/239687500000000000000000000 : ℝ)*base74 + (100502364086725543/15340000000000000000000000000000 : ℝ)*base76 + (186530459747245543/15340000000000000000000000000000 : ℝ)*base78 + (238525904971825543/15340000000000000000000000000000 : ℝ)*base80 + (10661568386517/3835000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (102282619/10000000000000000000000 : ℝ)*base89 + (102282619/10000000000000000000000 : ℝ)*base91 + (102282619/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3112976194364926334254701/590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (634413913/50000000000000 : ℝ)*(base19) + (97943847/6250000000000 : ℝ)*(base23) + (447873479/100000000000000 : ℝ)*(lower1) + (1681143/5000000000000 : ℝ)*(upper2) + (32762701/20000000000000 : ℝ)*(upper3) + (40717463/20000000000000 : ℝ)*(upper5) + (1682412062463873/50000000000000 : ℝ)*(major0) + (1682412062463873/50000000000000 : ℝ)*(major1) + (1682412062463873/50000000000000 : ℝ)*(major2) + (3345143593/50000000000000 : ℝ)*(sp2) + (2332542148117061/50000000000000 : ℝ)*(sp4) + (933016605481259/20000000000000 : ℝ)*(sp5) + (583134504855673/12500000000000 : ℝ)*(sp6) + (2064563777746999/100000000000000 : ℝ)*(sp7) + (2064563777746999/100000000000000 : ℝ)*(f.failure) + (2332542148117061/50000000000000 : ℝ)*(f.sum) + (6307594993/1152343750000000000000000 : ℝ)*base65 + (3393876676484433/1180000000000000000000000000000 : ℝ)*base67 + (30804041482015567/1180000000000000000000000000000 : ℝ)*base70 + (510992037984433/1180000000000000000000000000000 : ℝ)*base71 + (392908886867/295000000000000000000000000 : ℝ)*base74 + (11433161612964433/1180000000000000000000000000000 : ℝ)*base75 + (536746097335567/1180000000000000000000000000000 : ℝ)*base78 + (1566573509404433/1180000000000000000000000000000 : ℝ)*base79 + (3384751218001/147500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (33450907/10000000000000000000000 : ℝ)*base90 + (33450907/10000000000000000000000 : ℝ)*base92 + (33450907/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1507_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1507_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1507_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1507_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1507_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1507_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1507_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
