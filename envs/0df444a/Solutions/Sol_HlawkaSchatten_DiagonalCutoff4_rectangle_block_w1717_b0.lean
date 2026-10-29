-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1717_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:55:21.492637+00:00
-- url     : https://prove2.me/submissions/31d134e2-667e-426b-bafd-e58f7e32cb69

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
theorem support_rectangle_w1717_s0_0 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-329058683/2500000000 : ℝ)*x 0 + (5684067479/10000000000 : ℝ)*x 1 + (99349331/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329058683/2500000000 : ℝ)^5359 ≤ (815276741541/10000000000000 : ℝ)^4335 := by
    have hnat : (329058683 : ℕ)^5359*10000000000000^4335 ≤ 815276741541^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329058683 2500000000 815276741541 10000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5684067479/10000000000 : ℝ)^5359 ≤ (9947995914093/20000000000000 : ℝ)^4335 := by
    have hnat : (5684067479 : ℕ)^5359*20000000000000^4335 ≤ 9947995914093^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684067479 10000000000 9947995914093 20000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99349331/200000000 : ℝ)^5359 ≤ (10526813251943/25000000000000 : ℝ)^4335 := by
    have hnat : (99349331 : ℕ)^5359*25000000000000^4335 ≤ 10526813251943^4335*200000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99349331 200000000 10526813251943 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-329058683/2500000000 : ℝ), (5684067479/10000000000 : ℝ), (99349331/200000000 : ℝ)] ![(815276741541/10000000000000 : ℝ), (9947995914093/20000000000000 : ℝ), (10526813251943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-329058683/2500000000 : ℝ)|^5359 ≤ (815276741541/10000000000000 : ℝ)^4335
        have hw : |(-329058683/2500000000 : ℝ)|=(329058683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5684067479/10000000000 : ℝ)|^5359 ≤ (9947995914093/20000000000000 : ℝ)^4335
        have hw : |(5684067479/10000000000 : ℝ)|=(5684067479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(99349331/200000000 : ℝ)|^5359 ≤ (10526813251943/25000000000000 : ℝ)^4335
        have hw : |(99349331/200000000 : ℝ)|=(99349331/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s0_1 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337464247/625000000 : ℝ)*x 0 + (-425850799/2500000000 : ℝ)*x 1 + (993493181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337464247/625000000 : ℝ)^5359 ≤ (9335848116647/20000000000000 : ℝ)^4335 := by
    have hnat : (337464247 : ℕ)^5359*20000000000000^4335 ≤ 9335848116647^4335*625000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337464247 625000000 9335848116647 20000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425850799/2500000000 : ℝ)^5359 ≤ (5606756577903/50000000000000 : ℝ)^4335 := by
    have hnat : (425850799 : ℕ)^5359*50000000000000^4335 ≤ 5606756577903^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425850799 2500000000 5606756577903 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (993493181/2000000000 : ℝ)^5359 ≤ (42107246248867/100000000000000 : ℝ)^4335 := by
    have hnat : (993493181 : ℕ)^5359*100000000000000^4335 ≤ 42107246248867^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993493181 2000000000 42107246248867 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337464247/625000000 : ℝ), (-425850799/2500000000 : ℝ), (993493181/2000000000 : ℝ)] ![(9335848116647/20000000000000 : ℝ), (5606756577903/50000000000000 : ℝ), (42107246248867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337464247/625000000 : ℝ)|^5359 ≤ (9335848116647/20000000000000 : ℝ)^4335
        have hw : |(337464247/625000000 : ℝ)|=(337464247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425850799/2500000000 : ℝ)|^5359 ≤ (5606756577903/50000000000000 : ℝ)^4335
        have hw : |(-425850799/2500000000 : ℝ)|=(425850799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(993493181/2000000000 : ℝ)|^5359 ≤ (42107246248867/100000000000000 : ℝ)^4335
        have hw : |(993493181/2000000000 : ℝ)|=(993493181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s0_2 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699713759/5000000000 : ℝ)*x 0 + (4967466587/10000000000 : ℝ)*x 1 + (-212925361/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699713759/5000000000 : ℝ)^5359 ≤ (23339617972459/50000000000000 : ℝ)^4335 := by
    have hnat : (2699713759 : ℕ)^5359*50000000000000^4335 ≤ 23339617972459^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699713759 5000000000 23339617972459 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4967466587/10000000000 : ℝ)^5359 ≤ (10526813348873/25000000000000 : ℝ)^4335 := by
    have hnat : (4967466587 : ℕ)^5359*25000000000000^4335 ≤ 10526813348873^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4967466587 10000000000 10526813348873 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212925361/1250000000 : ℝ)^5359 ≤ (2242702129859/20000000000000 : ℝ)^4335 := by
    have hnat : (212925361 : ℕ)^5359*20000000000000^4335 ≤ 2242702129859^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212925361 1250000000 2242702129859 20000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699713759/5000000000 : ℝ), (4967466587/10000000000 : ℝ), (-212925361/1250000000 : ℝ)] ![(23339617972459/50000000000000 : ℝ), (10526813348873/25000000000000 : ℝ), (2242702129859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699713759/5000000000 : ℝ)|^5359 ≤ (23339617972459/50000000000000 : ℝ)^4335
        have hw : |(2699713759/5000000000 : ℝ)|=(2699713759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4967466587/10000000000 : ℝ)|^5359 ≤ (10526813348873/25000000000000 : ℝ)^4335
        have hw : |(4967466587/10000000000 : ℝ)|=(4967466587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212925361/1250000000 : ℝ)|^5359 ≤ (2242702129859/20000000000000 : ℝ)^4335
        have hw : |(-212925361/1250000000 : ℝ)|=(212925361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s0_3 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4033734927/10000000000 : ℝ)*x 0 + (191460361/625000000 : ℝ)*x 1 + (1034833091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4033734927/10000000000 : ℝ)^5359 ≤ (16275667072017/50000000000000 : ℝ)^4335 := by
    have hnat : (4033734927 : ℕ)^5359*50000000000000^4335 ≤ 16275667072017^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033734927 10000000000 16275667072017 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191460361/625000000 : ℝ)^5359 ≤ (23164897008583/100000000000000 : ℝ)^4335 := by
    have hnat : (191460361 : ℕ)^5359*100000000000000^4335 ≤ 23164897008583^4335*625000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191460361 625000000 23164897008583 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034833091/2000000000 : ℝ)^5359 ≤ (44283768827861/100000000000000 : ℝ)^4335 := by
    have hnat : (1034833091 : ℕ)^5359*100000000000000^4335 ≤ 44283768827861^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034833091 2000000000 44283768827861 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4033734927/10000000000 : ℝ), (191460361/625000000 : ℝ), (1034833091/2000000000 : ℝ)] ![(16275667072017/50000000000000 : ℝ), (23164897008583/100000000000000 : ℝ), (44283768827861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4033734927/10000000000 : ℝ)|^5359 ≤ (16275667072017/50000000000000 : ℝ)^4335
        have hw : |(4033734927/10000000000 : ℝ)|=(4033734927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191460361/625000000 : ℝ)|^5359 ≤ (23164897008583/100000000000000 : ℝ)^4335
        have hw : |(191460361/625000000 : ℝ)|=(191460361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034833091/2000000000 : ℝ)|^5359 ≤ (44283768827861/100000000000000 : ℝ)^4335
        have hw : |(1034833091/2000000000 : ℝ)|=(1034833091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s0_4 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1317797787/10000000000 : ℝ)*x 0 + (4984941447/10000000000 : ℝ)*x 1 + (1416504939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317797787/10000000000 : ℝ)^5359 ≤ (4082368809147/50000000000000 : ℝ)^4335 := by
    have hnat : (1317797787 : ℕ)^5359*50000000000000^4335 ≤ 4082368809147^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317797787 10000000000 4082368809147 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4984941447/10000000000 : ℝ)^5359 ≤ (21145223554317/50000000000000 : ℝ)^4335 := by
    have hnat : (4984941447 : ℕ)^5359*50000000000000^4335 ≤ 21145223554317^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984941447 10000000000 21145223554317 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1416504939/2500000000 : ℝ)^5359 ≤ (12386203812723/25000000000000 : ℝ)^4335 := by
    have hnat : (1416504939 : ℕ)^5359*25000000000000^4335 ≤ 12386203812723^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416504939 2500000000 12386203812723 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1317797787/10000000000 : ℝ), (4984941447/10000000000 : ℝ), (1416504939/2500000000 : ℝ)] ![(4082368809147/50000000000000 : ℝ), (21145223554317/50000000000000 : ℝ), (12386203812723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1317797787/10000000000 : ℝ)|^5359 ≤ (4082368809147/50000000000000 : ℝ)^4335
        have hw : |(-1317797787/10000000000 : ℝ)|=(1317797787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4984941447/10000000000 : ℝ)|^5359 ≤ (21145223554317/50000000000000 : ℝ)^4335
        have hw : |(4984941447/10000000000 : ℝ)|=(4984941447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1416504939/2500000000 : ℝ)|^5359 ≤ (12386203812723/25000000000000 : ℝ)^4335
        have hw : |(1416504939/2500000000 : ℝ)|=(1416504939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s0_5 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5205507053/10000000000 : ℝ)*x 0 + (-50242517/500000000 : ℝ)*x 1 + (5666020129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5205507053/10000000000 : ℝ)^5359 ≤ (44615609923601/100000000000000 : ℝ)^4335 := by
    have hnat : (5205507053 : ℕ)^5359*100000000000000^4335 ≤ 44615609923601^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205507053 10000000000 44615609923601 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50242517/500000000 : ℝ)^5359 ≤ (1459892693567/25000000000000 : ℝ)^4335 := by
    have hnat : (50242517 : ℕ)^5359*25000000000000^4335 ≤ 1459892693567^4335*500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50242517 500000000 1459892693567 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5666020129/10000000000 : ℝ)^5359 ≤ (49544819282921/100000000000000 : ℝ)^4335 := by
    have hnat : (5666020129 : ℕ)^5359*100000000000000^4335 ≤ 49544819282921^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666020129 10000000000 49544819282921 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5205507053/10000000000 : ℝ), (-50242517/500000000 : ℝ), (5666020129/10000000000 : ℝ)] ![(44615609923601/100000000000000 : ℝ), (1459892693567/25000000000000 : ℝ), (49544819282921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5205507053/10000000000 : ℝ)|^5359 ≤ (44615609923601/100000000000000 : ℝ)^4335
        have hw : |(5205507053/10000000000 : ℝ)|=(5205507053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50242517/500000000 : ℝ)|^5359 ≤ (1459892693567/25000000000000 : ℝ)^4335
        have hw : |(-50242517/500000000 : ℝ)|=(50242517/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5666020129/10000000000 : ℝ)|^5359 ≤ (49544819282921/100000000000000 : ℝ)^4335
        have hw : |(5666020129/10000000000 : ℝ)|=(5666020129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s0_6 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5205508031/10000000000 : ℝ)*x 0 + (5666019281/10000000000 : ℝ)*x 1 + (-502425087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5205508031/10000000000 : ℝ)^5359 ≤ (5576952535741/12500000000000 : ℝ)^4335 := by
    have hnat : (5205508031 : ℕ)^5359*12500000000000^4335 ≤ 5576952535741^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205508031 10000000000 5576952535741 12500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5666019281/10000000000 : ℝ)^5359 ≤ (49544810116271/100000000000000 : ℝ)^4335 := by
    have hnat : (5666019281 : ℕ)^5359*100000000000000^4335 ≤ 49544810116271^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666019281 10000000000 49544810116271 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502425087/5000000000 : ℝ)^5359 ≤ (5839569581703/100000000000000 : ℝ)^4335 := by
    have hnat : (502425087 : ℕ)^5359*100000000000000^4335 ≤ 5839569581703^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502425087 5000000000 5839569581703 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5205508031/10000000000 : ℝ), (5666019281/10000000000 : ℝ), (-502425087/5000000000 : ℝ)] ![(5576952535741/12500000000000 : ℝ), (49544810116271/100000000000000 : ℝ), (5839569581703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5205508031/10000000000 : ℝ)|^5359 ≤ (5576952535741/12500000000000 : ℝ)^4335
        have hw : |(5205508031/10000000000 : ℝ)|=(5205508031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5666019281/10000000000 : ℝ)|^5359 ≤ (49544810116271/100000000000000 : ℝ)^4335
        have hw : |(5666019281/10000000000 : ℝ)|=(5666019281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-502425087/5000000000 : ℝ)|^5359 ≤ (5839569581703/100000000000000 : ℝ)^4335
        have hw : |(-502425087/5000000000 : ℝ)|=(502425087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s0_7 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1009585731/2500000000 : ℝ)*x 0 + (2561345823/5000000000 : ℝ)*x 1 + (779132247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009585731/2500000000 : ℝ)^5359 ≤ (16298654842913/50000000000000 : ℝ)^4335 := by
    have hnat : (1009585731 : ℕ)^5359*50000000000000^4335 ≤ 16298654842913^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009585731 2500000000 16298654842913 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2561345823/5000000000 : ℝ)^5359 ≤ (21869900420283/50000000000000 : ℝ)^4335 := by
    have hnat : (2561345823 : ℕ)^5359*50000000000000^4335 ≤ 21869900420283^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561345823 5000000000 21869900420283 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (779132247/2500000000 : ℝ)^5359 ≤ (11831444728931/50000000000000 : ℝ)^4335 := by
    have hnat : (779132247 : ℕ)^5359*50000000000000^4335 ≤ 11831444728931^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779132247 2500000000 11831444728931 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1009585731/2500000000 : ℝ), (2561345823/5000000000 : ℝ), (779132247/2500000000 : ℝ)] ![(16298654842913/50000000000000 : ℝ), (21869900420283/50000000000000 : ℝ), (11831444728931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1009585731/2500000000 : ℝ)|^5359 ≤ (16298654842913/50000000000000 : ℝ)^4335
        have hw : |(1009585731/2500000000 : ℝ)|=(1009585731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2561345823/5000000000 : ℝ)|^5359 ≤ (21869900420283/50000000000000 : ℝ)^4335
        have hw : |(2561345823/5000000000 : ℝ)|=(2561345823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(779132247/2500000000 : ℝ)|^5359 ≤ (11831444728931/50000000000000 : ℝ)^4335
        have hw : |(779132247/2500000000 : ℝ)|=(779132247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1717_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1/16 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21667/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5351/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5351 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5351*1^1024 ≤ 0^1024*1^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5351/1024 : ℝ) ≤ (208195000038414449/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5351 ≤ (208195000038414449/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5351*25000000000000000000^1024 ≤ 208195000038414449^1024*5^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 208195000038414449 25000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (208195000038414449/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5351 := by
      have hnat : (1 : ℕ)^1024*1^5351 ≤ 1^5351*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25208195000038414449/25000000000000000000 : ℝ) ≤ (5007941597145121/5000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (25208195000038414449/25000000000000000000 : ℝ)^1024 ≤ (5007941597145121/5000000000000000 : ℝ)^5351 := by
      have hnat : (25208195000038414449 : ℕ)^1024*5000000000000000^5351 ≤ 5007941597145121^5351*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25208195000038414449 25000000000000000000 5007941597145121 5000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007941597145121/5000000000000000 : ℝ)) (X := (25208195000038414449/25000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12708195000038414449/12500000000000000000 : ℝ) ≤ (2507941597145121/2500000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (12708195000038414449/12500000000000000000 : ℝ)^1024 ≤ (2507941597145121/2500000000000000 : ℝ)^5351 := by
      have hnat : (12708195000038414449 : ℕ)^1024*2500000000000000^5351 ≤ 2507941597145121^5351*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12708195000038414449 12500000000000000000 2507941597145121 2500000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507941597145121/2500000000000000 : ℝ)) (X := (12708195000038414449/12500000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7941597145121/2000000000000000 : ℝ)*(0 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7941597145121/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(208195000038414449/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7941597145121/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5351/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7941597145121/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5007941597145121/5000000000000000 : ℝ) by norm_num, show 1+(208195000038414449/25000000000000000000 : ℝ)+(0 : ℝ)=(25208195000038414449/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(208195000038414449/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7941597145121/2000000000000000 : ℝ)*(2/5 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7941597145121/2000000000000000 : ℝ)*(2/5 : ℝ)=(2507941597145121/2500000000000000 : ℝ) by norm_num, show 1+2*(208195000038414449/25000000000000000000 : ℝ)=(12708195000038414449/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7941597145121/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7941597145121/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7941597145121/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7941597145121/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7941597145121/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7941597145121/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-329058683/2500000000 : ℝ)*X 0 0+(5684067479/10000000000 : ℝ)*X 0 1+(99349331/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((337464247/625000000 : ℝ)*X 1 0+(-425850799/2500000000 : ℝ)*X 1 1+(993493181/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2699713759/5000000000 : ℝ)*X 2 0+(4967466587/10000000000 : ℝ)*X 2 1+(-212925361/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4033734927/10000000000 : ℝ)*X 0 0+(191460361/625000000 : ℝ)*X 0 1+(1034833091/2000000000 : ℝ)*X 0 2+(4033734927/10000000000 : ℝ)*X 1 0+(191460361/625000000 : ℝ)*X 1 1+(1034833091/2000000000 : ℝ)*X 1 2+(4033734927/10000000000 : ℝ)*X 2 0+(191460361/625000000 : ℝ)*X 2 1+(1034833091/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1317797787/10000000000 : ℝ)*X 0 0+(4984941447/10000000000 : ℝ)*X 0 1+(1416504939/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5205507053/10000000000 : ℝ)*X 1 0+(-50242517/500000000 : ℝ)*X 1 1+(5666020129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5205508031/10000000000 : ℝ)*X 2 0+(5666019281/10000000000 : ℝ)*X 2 1+(-502425087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1009585731/2500000000 : ℝ)*X 0 0+(2561345823/5000000000 : ℝ)*X 0 1+(779132247/2500000000 : ℝ)*X 0 2+(1009585731/2500000000 : ℝ)*X 1 0+(2561345823/5000000000 : ℝ)*X 1 1+(779132247/2500000000 : ℝ)*X 1 2+(1009585731/2500000000 : ℝ)*X 2 0+(2561345823/5000000000 : ℝ)*X 2 1+(779132247/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (379807377991756958974527/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149441047/100000000000000 : ℝ)*(base1) + (1307820341/100000000000000 : ℝ)*(base19) + (1195652819/100000000000000 : ℝ)*(base23) + (15458139/12500000000000 : ℝ)*(upper3) + (113997279/50000000000000 : ℝ)*(upper5) + (467310955624343/50000000000000 : ℝ)*(major0) + (467310955624343/50000000000000 : ℝ)*(major1) + (467310955624343/50000000000000 : ℝ)*(major2) + (279096192431513/20000000000000 : ℝ)*(sp0) + (1395484805233167/100000000000000 : ℝ)*(sp1) + (1395484917400689/100000000000000 : ℝ)*(sp2) + (473755857534873/100000000000000 : ℝ)*(sp3) + (530033699/10000000000000 : ℝ)*(sp4) + (724631511/50000000000000 : ℝ)*(sp7) + (473757456238941/100000000000000 : ℝ)*(f.failure) + (348871528263377/25000000000000 : ℝ)*(f.sum) + (89481913169497/50000000000000000000000000000 : ℝ)*base66 + (174749548780503/100000000000000000000000000000 : ℝ)*base67 + (691154982819497/100000000000000000000000000000 : ℝ)*base70 + (53958027019497/100000000000000000000000000000 : ℝ)*base72 + (108204015119497/50000000000000000000000000000 : ℝ)*base74 + (79469577319497/100000000000000000000000000000 : ℝ)*base76 + (1894381180503/100000000000000000000000000000 : ℝ)*base77 + (365777020980503/100000000000000000000000000000 : ℝ)*base79 + (228218274669497/50000000000000000000000000000 : ℝ)*base82 + (4480067/2000000000000000000000 : ℝ)*base90 + (4480067/2000000000000000000000 : ℝ)*base92 + (4480067/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61984103333557986999099/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8872743/12500000000000 : ℝ)*(base1) + (39842589/4000000000000 : ℝ)*(base19) + (1342769569/100000000000000 : ℝ)*(base23) + (8060581/1250000000000 : ℝ)*(base32) + (301260071/100000000000000 : ℝ)*(upper3) + (98336007004727/10000000000000 : ℝ)*(major0) + (98336007004727/10000000000000 : ℝ)*(major1) + (98336007004727/10000000000000 : ℝ)*(major2) + (415085469/20000000000000 : ℝ)*(sp1) + (3977368173/100000000000000 : ℝ)*(sp2) + (91766068348593/6250000000000 : ℝ)*(sp4) + (1468253951103473/100000000000000 : ℝ)*(sp5) + (734125851228901/50000000000000 : ℝ)*(sp6) + (62307748555401/12500000000000 : ℝ)*(sp7) + (31153919016977/6250000000000 : ℝ)*(f.failure) + (183532127824443/12500000000000 : ℝ)*(f.sum) + (6569140626967/10000000000000000000000000000 : ℝ)*base65 + (66513841906967/20000000000000000000000000000 : ℝ)*base67 + (190369776653033/20000000000000000000000000000 : ℝ)*base70 + (67099497966967/20000000000000000000000000000 : ℝ)*base71 + (44511402706967/10000000000000000000000000000 : ℝ)*base73 + (76687677066967/20000000000000000000000000000 : ℝ)*base75 + (102715501373033/20000000000000000000000000000 : ℝ)*base78 + (119348426366967/20000000000000000000000000000 : ℝ)*base79 + (37687171333033/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (860399/125000000000000000000 : ℝ)*base90 + (860399/125000000000000000000 : ℝ)*base92 + (860399/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1717_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1/16 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21667/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1717_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1717_s1_0 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-692034623/5000000000 : ℝ)*x 0 + (219135897/400000000 : ℝ)*x 1 + (5128396411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (692034623/5000000000 : ℝ)^5359 ≤ (8675306609211/100000000000000 : ℝ)^4335 := by
    have hnat : (692034623 : ℕ)^5359*100000000000000^4335 ≤ 8675306609211^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692034623 5000000000 8675306609211 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219135897/400000000 : ℝ)^5359 ≤ (23762334370023/50000000000000 : ℝ)^4335 := by
    have hnat : (219135897 : ℕ)^5359*50000000000000^4335 ≤ 23762334370023^4335*400000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219135897 400000000 23762334370023 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128396411/10000000000 : ℝ)^5359 ≤ (10950006158327/25000000000000 : ℝ)^4335 := by
    have hnat : (5128396411 : ℕ)^5359*25000000000000^4335 ≤ 10950006158327^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128396411 10000000000 10950006158327 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-692034623/5000000000 : ℝ), (219135897/400000000 : ℝ), (5128396411/10000000000 : ℝ)] ![(8675306609211/100000000000000 : ℝ), (23762334370023/50000000000000 : ℝ), (10950006158327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-692034623/5000000000 : ℝ)|^5359 ≤ (8675306609211/100000000000000 : ℝ)^4335
        have hw : |(-692034623/5000000000 : ℝ)|=(692034623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219135897/400000000 : ℝ)|^5359 ≤ (23762334370023/50000000000000 : ℝ)^4335
        have hw : |(219135897/400000000 : ℝ)|=(219135897/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128396411/10000000000 : ℝ)|^5359 ≤ (10950006158327/25000000000000 : ℝ)^4335
        have hw : |(5128396411/10000000000 : ℝ)|=(5128396411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s1_1 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672324027/5000000000 : ℝ)*x 0 + (-782955633/5000000000 : ℝ)*x 1 + (5128395397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672324027/5000000000 : ℝ)^5359 ≤ (46094491108371/100000000000000 : ℝ)^4335 := by
    have hnat : (2672324027 : ℕ)^5359*100000000000000^4335 ≤ 46094491108371^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672324027 5000000000 46094491108371 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782955633/5000000000 : ℝ)^5359 ≤ (5052747474337/50000000000000 : ℝ)^4335 := by
    have hnat : (782955633 : ℕ)^5359*50000000000000^4335 ≤ 5052747474337^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782955633 5000000000 5052747474337 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128395397/10000000000 : ℝ)^5359 ≤ (21900006963677/50000000000000 : ℝ)^4335 := by
    have hnat : (5128395397 : ℕ)^5359*50000000000000^4335 ≤ 21900006963677^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128395397 10000000000 21900006963677 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672324027/5000000000 : ℝ), (-782955633/5000000000 : ℝ), (5128395397/10000000000 : ℝ)] ![(46094491108371/100000000000000 : ℝ), (5052747474337/50000000000000 : ℝ), (21900006963677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672324027/5000000000 : ℝ)|^5359 ≤ (46094491108371/100000000000000 : ℝ)^4335
        have hw : |(2672324027/5000000000 : ℝ)|=(2672324027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-782955633/5000000000 : ℝ)|^5359 ≤ (5052747474337/50000000000000 : ℝ)^4335
        have hw : |(-782955633/5000000000 : ℝ)|=(782955633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128395397/10000000000 : ℝ)|^5359 ≤ (21900006963677/50000000000000 : ℝ)^4335
        have hw : |(5128395397/10000000000 : ℝ)|=(5128395397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s1_2 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344646791/10000000000 : ℝ)*x 0 + (5128396393/10000000000 : ℝ)*x 1 + (-391477909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344646791/10000000000 : ℝ)^5359 ≤ (46094477642703/100000000000000 : ℝ)^4335 := by
    have hnat : (5344646791 : ℕ)^5359*100000000000000^4335 ≤ 46094477642703^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344646791 10000000000 46094477642703 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128396393/10000000000 : ℝ)^5359 ≤ (21900012221631/50000000000000 : ℝ)^4335 := by
    have hnat : (5128396393 : ℕ)^5359*50000000000000^4335 ≤ 21900012221631^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128396393 10000000000 21900012221631 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391477909/2500000000 : ℝ)^5359 ≤ (5052748950237/50000000000000 : ℝ)^4335 := by
    have hnat : (391477909 : ℕ)^5359*50000000000000^4335 ≤ 5052748950237^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391477909 2500000000 5052748950237 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344646791/10000000000 : ℝ), (5128396393/10000000000 : ℝ), (-391477909/2500000000 : ℝ)] ![(46094477642703/100000000000000 : ℝ), (21900012221631/50000000000000 : ℝ), (5052748950237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344646791/10000000000 : ℝ)|^5359 ≤ (46094477642703/100000000000000 : ℝ)^4335
        have hw : |(5344646791/10000000000 : ℝ)|=(5344646791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128396393/10000000000 : ℝ)|^5359 ≤ (21900012221631/50000000000000 : ℝ)^4335
        have hw : |(5128396393/10000000000 : ℝ)|=(5128396393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391477909/2500000000 : ℝ)|^5359 ≤ (5052748950237/50000000000000 : ℝ)^4335
        have hw : |(-391477909/2500000000 : ℝ)|=(391477909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s1_3 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2046706463/5000000000 : ℝ)*x 0 + (719617501/2000000000 : ℝ)*x 1 + (462903717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046706463/5000000000 : ℝ)^5359 ≤ (33147717791257/100000000000000 : ℝ)^4335 := by
    have hnat : (2046706463 : ℕ)^5359*100000000000000^4335 ≤ 33147717791257^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046706463 5000000000 33147717791257 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719617501/2000000000 : ℝ)^5359 ≤ (3532794690859/12500000000000 : ℝ)^4335 := by
    have hnat : (719617501 : ℕ)^5359*12500000000000^4335 ≤ 3532794690859^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719617501 2000000000 3532794690859 12500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462903717/1000000000 : ℝ)^5359 ≤ (4823740584191/12500000000000 : ℝ)^4335 := by
    have hnat : (462903717 : ℕ)^5359*12500000000000^4335 ≤ 4823740584191^4335*1000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462903717 1000000000 4823740584191 12500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2046706463/5000000000 : ℝ), (719617501/2000000000 : ℝ), (462903717/1000000000 : ℝ)] ![(33147717791257/100000000000000 : ℝ), (3532794690859/12500000000000 : ℝ), (4823740584191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2046706463/5000000000 : ℝ)|^5359 ≤ (33147717791257/100000000000000 : ℝ)^4335
        have hw : |(2046706463/5000000000 : ℝ)|=(2046706463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(719617501/2000000000 : ℝ)|^5359 ≤ (3532794690859/12500000000000 : ℝ)^4335
        have hw : |(719617501/2000000000 : ℝ)|=(719617501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(462903717/1000000000 : ℝ)|^5359 ≤ (4823740584191/12500000000000 : ℝ)^4335
        have hw : |(462903717/1000000000 : ℝ)|=(462903717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s1_4 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-692125853/5000000000 : ℝ)*x 0 + (1026514787/2000000000 : ℝ)*x 1 + (1368537981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (692125853/5000000000 : ℝ)^5359 ≤ (8676720435659/100000000000000 : ℝ)^4335 := by
    have hnat : (692125853 : ℕ)^5359*100000000000000^4335 ≤ 8676720435659^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692125853 5000000000 8676720435659 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026514787/2000000000 : ℝ)^5359 ≤ (21922067879893/50000000000000 : ℝ)^4335 := by
    have hnat : (1026514787 : ℕ)^5359*50000000000000^4335 ≤ 21922067879893^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026514787 2000000000 21922067879893 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368537981/2500000000 : ℝ)^5359 ≤ (47479143797473/100000000000000 : ℝ)^4335 := by
    have hnat : (1368537981 : ℕ)^5359*100000000000000^4335 ≤ 47479143797473^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368537981 2500000000 47479143797473 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-692125853/5000000000 : ℝ), (1026514787/2000000000 : ℝ), (1368537981/2500000000 : ℝ)] ![(8676720435659/100000000000000 : ℝ), (21922067879893/50000000000000 : ℝ), (47479143797473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-692125853/5000000000 : ℝ)|^5359 ≤ (8676720435659/100000000000000 : ℝ)^4335
        have hw : |(-692125853/5000000000 : ℝ)|=(692125853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026514787/2000000000 : ℝ)|^5359 ≤ (21922067879893/50000000000000 : ℝ)^4335
        have hw : |(1026514787/2000000000 : ℝ)|=(1026514787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368537981/2500000000 : ℝ)|^5359 ≤ (47479143797473/100000000000000 : ℝ)^4335
        have hw : |(1368537981/2500000000 : ℝ)|=(1368537981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s1_5 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250924561/10000000000 : ℝ)*x 0 + (-1220155301/10000000000 : ℝ)*x 1 + (109483029/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250924561/10000000000 : ℝ)^5359 ≤ (22548661294683/50000000000000 : ℝ)^4335 := by
    have hnat : (5250924561 : ℕ)^5359*50000000000000^4335 ≤ 22548661294683^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250924561 10000000000 22548661294683 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220155301/10000000000 : ℝ)^5359 ≤ (927942335169/12500000000000 : ℝ)^4335 := by
    have hnat : (1220155301 : ℕ)^5359*12500000000000^4335 ≤ 927942335169^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220155301 10000000000 927942335169 12500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109483029/200000000 : ℝ)^5359 ≤ (11869784678797/25000000000000 : ℝ)^4335 := by
    have hnat : (109483029 : ℕ)^5359*25000000000000^4335 ≤ 11869784678797^4335*200000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109483029 200000000 11869784678797 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250924561/10000000000 : ℝ), (-1220155301/10000000000 : ℝ), (109483029/200000000 : ℝ)] ![(22548661294683/50000000000000 : ℝ), (927942335169/12500000000000 : ℝ), (11869784678797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250924561/10000000000 : ℝ)|^5359 ≤ (22548661294683/50000000000000 : ℝ)^4335
        have hw : |(5250924561/10000000000 : ℝ)|=(5250924561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1220155301/10000000000 : ℝ)|^5359 ≤ (927942335169/12500000000000 : ℝ)^4335
        have hw : |(-1220155301/10000000000 : ℝ)|=(1220155301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109483029/200000000 : ℝ)|^5359 ≤ (11869784678797/25000000000000 : ℝ)^4335
        have hw : |(109483029/200000000 : ℝ)|=(109483029/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s1_6 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250924843/10000000000 : ℝ)*x 0 + (2737075549/5000000000 : ℝ)*x 1 + (-244031081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250924843/10000000000 : ℝ)^5359 ≤ (45097325583413/100000000000000 : ℝ)^4335 := by
    have hnat : (5250924843 : ℕ)^5359*100000000000000^4335 ≤ 45097325583413^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250924843 10000000000 45097325583413 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737075549/5000000000 : ℝ)^5359 ≤ (23739567470501/50000000000000 : ℝ)^4335 := by
    have hnat : (2737075549 : ℕ)^5359*50000000000000^4335 ≤ 23739567470501^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737075549 5000000000 23739567470501 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244031081/2000000000 : ℝ)^5359 ≤ (7423539463563/100000000000000 : ℝ)^4335 := by
    have hnat : (244031081 : ℕ)^5359*100000000000000^4335 ≤ 7423539463563^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244031081 2000000000 7423539463563 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250924843/10000000000 : ℝ), (2737075549/5000000000 : ℝ), (-244031081/2000000000 : ℝ)] ![(45097325583413/100000000000000 : ℝ), (23739567470501/50000000000000 : ℝ), (7423539463563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250924843/10000000000 : ℝ)|^5359 ≤ (45097325583413/100000000000000 : ℝ)^4335
        have hw : |(5250924843/10000000000 : ℝ)|=(5250924843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737075549/5000000000 : ℝ)|^5359 ≤ (23739567470501/50000000000000 : ℝ)^4335
        have hw : |(2737075549/5000000000 : ℝ)|=(2737075549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244031081/2000000000 : ℝ)|^5359 ≤ (7423539463563/100000000000000 : ℝ)^4335
        have hw : |(-244031081/2000000000 : ℝ)|=(244031081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s1_7 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2046972857/5000000000 : ℝ)*x 0 + (923346219/2000000000 : ℝ)*x 1 + (451323711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046972857/5000000000 : ℝ)^5359 ≤ (33153051433011/100000000000000 : ℝ)^4335 := by
    have hnat : (2046972857 : ℕ)^5359*100000000000000^4335 ≤ 33153051433011^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046972857 5000000000 33153051433011 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (923346219/2000000000 : ℝ)^5359 ≤ (9615785420171/25000000000000 : ℝ)^4335 := by
    have hnat : (923346219 : ℕ)^5359*25000000000000^4335 ≤ 9615785420171^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923346219 2000000000 9615785420171 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451323711/1250000000 : ℝ)^5359 ≤ (14191903440169/50000000000000 : ℝ)^4335 := by
    have hnat : (451323711 : ℕ)^5359*50000000000000^4335 ≤ 14191903440169^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451323711 1250000000 14191903440169 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2046972857/5000000000 : ℝ), (923346219/2000000000 : ℝ), (451323711/1250000000 : ℝ)] ![(33153051433011/100000000000000 : ℝ), (9615785420171/25000000000000 : ℝ), (14191903440169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2046972857/5000000000 : ℝ)|^5359 ≤ (33153051433011/100000000000000 : ℝ)^4335
        have hw : |(2046972857/5000000000 : ℝ)|=(2046972857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(923346219/2000000000 : ℝ)|^5359 ≤ (9615785420171/25000000000000 : ℝ)^4335
        have hw : |(923346219/2000000000 : ℝ)|=(923346219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451323711/1250000000 : ℝ)|^5359 ≤ (14191903440169/50000000000000 : ℝ)^4335
        have hw : |(451323711/1250000000 : ℝ)|=(451323711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1717_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/16 : ℝ)*pair X i i ≤ pair X i h) :
    (9831/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (541/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1/16 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1/16 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1/16 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1/16 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1/16 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1/16 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1/16 : ℝ) ^ (5351/1024 : ℝ) ≤ (51023183432591/100000000000000000000 : ℝ) := by
    have hpowers : (1/16 : ℝ)^5351 ≤ (51023183432591/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1 : ℕ)^5351*100000000000000000000^1024 ≤ 51023183432591^1024*16^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 16 51023183432591 100000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1/16 : ℝ)) (X := (51023183432591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21667/100000 : ℝ) ^ (5351/1024 : ℝ) ≤ (33818898826364831/100000000000000000000 : ℝ) := by
    have hpowers : (21667/100000 : ℝ)^5351 ≤ (33818898826364831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (21667 : ℕ)^5351*100000000000000000000^1024 ≤ 33818898826364831^1024*100000^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21667 100000 33818898826364831 100000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21667/100000 : ℝ)) (X := (33818898826364831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051023183432591/50000000000000000000 : ℝ) ≤ (10000001952820717/10000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50000051023183432591/50000000000000000000 : ℝ)^1024 ≤ (10000001952820717/10000000000000000 : ℝ)^5351 := by
      have hnat : (50000051023183432591 : ℕ)^1024*10000000000000000^5351 ≤ 10000001952820717^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051023183432591 50000000000000000000 10000001952820717 10000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001952820717/10000000000000000 : ℝ)) (X := (50000051023183432591/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016934961004898711/50000000000000000000 : ℝ) ≤ (5000324033373027/5000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50016934961004898711/50000000000000000000 : ℝ)^1024 ≤ (5000324033373027/5000000000000000 : ℝ)^5351 := by
      have hnat : (50016934961004898711 : ℕ)^1024*5000000000000000^5351 ≤ 5000324033373027^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016934961004898711 50000000000000000000 5000324033373027 5000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000324033373027/5000000000000000 : ℝ)) (X := (50016934961004898711/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033818898826364831/50000000000000000000 : ℝ) ≤ (10001294180671391/10000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50033818898826364831/50000000000000000000 : ℝ)^1024 ≤ (10001294180671391/10000000000000000 : ℝ)^5351 := by
      have hnat : (50033818898826364831 : ℕ)^1024*10000000000000000^5351 ≤ 10001294180671391^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033818898826364831 50000000000000000000 10001294180671391 10000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001294180671391/10000000000000000 : ℝ)) (X := (50033818898826364831/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51023183432591/100000000000000000000 : ℝ) ≤ ((154161953682570281489/154170000000000000000 : ℝ)+2*(646113925337/1541700000000000 : ℝ)*(1/16 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (154161953682570281489/154170000000000000000 : ℝ)+2*(646113925337/1541700000000000 : ℝ)*(1/16 : ℝ)=(10000001952820717/10000000000000000 : ℝ) by norm_num, show 1+2*(51023183432591/100000000000000000000 : ℝ)=(50000051023183432591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33818898826364831/100000000000000000000 : ℝ)+(51023183432591/100000000000000000000 : ℝ) ≤ ((154161953682570281489/154170000000000000000 : ℝ)+(646113925337/1541700000000000 : ℝ)*((21667/100000 : ℝ)+(1/16 : ℝ)))^(5351/1024 : ℝ) := by
    rw [show (154161953682570281489/154170000000000000000 : ℝ)+(646113925337/1541700000000000 : ℝ)*((21667/100000 : ℝ)+(1/16 : ℝ))=(5000324033373027/5000000000000000 : ℝ) by norm_num, show 1+(33818898826364831/100000000000000000000 : ℝ)+(51023183432591/100000000000000000000 : ℝ)=(50016934961004898711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33818898826364831/100000000000000000000 : ℝ) ≤ ((154161953682570281489/154170000000000000000 : ℝ)+2*(646113925337/1541700000000000 : ℝ)*(21667/100000 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (154161953682570281489/154170000000000000000 : ℝ)+2*(646113925337/1541700000000000 : ℝ)*(21667/100000 : ℝ)=(10001294180671391/10000000000000000 : ℝ) by norm_num, show 1+2*(33818898826364831/100000000000000000000 : ℝ)=(50033818898826364831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (154161953682570281489/154170000000000000000 : ℝ)*(X 1 0+X 2 0)+(646113925337/1541700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (1/16 : ℝ)) (hi := (21667/100000 : ℝ)) (c := (154161953682570281489/154170000000000000000 : ℝ)) (alpha := (646113925337/1541700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (154161953682570281489/154170000000000000000 : ℝ)*(X 0 1+X 2 1)+(646113925337/1541700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (1/16 : ℝ)) (hi := (21667/100000 : ℝ)) (c := (154161953682570281489/154170000000000000000 : ℝ)) (alpha := (646113925337/1541700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (154161953682570281489/154170000000000000000 : ℝ)*(X 0 2+X 1 2)+(646113925337/1541700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (1/16 : ℝ)) (hi := (21667/100000 : ℝ)) (c := (154161953682570281489/154170000000000000000 : ℝ)) (alpha := (646113925337/1541700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-692034623/5000000000 : ℝ)*X 0 0+(219135897/400000000 : ℝ)*X 0 1+(5128396411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672324027/5000000000 : ℝ)*X 1 0+(-782955633/5000000000 : ℝ)*X 1 1+(5128395397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344646791/10000000000 : ℝ)*X 2 0+(5128396393/10000000000 : ℝ)*X 2 1+(-391477909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2046706463/5000000000 : ℝ)*X 0 0+(719617501/2000000000 : ℝ)*X 0 1+(462903717/1000000000 : ℝ)*X 0 2+(2046706463/5000000000 : ℝ)*X 1 0+(719617501/2000000000 : ℝ)*X 1 1+(462903717/1000000000 : ℝ)*X 1 2+(2046706463/5000000000 : ℝ)*X 2 0+(719617501/2000000000 : ℝ)*X 2 1+(462903717/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-692125853/5000000000 : ℝ)*X 0 0+(1026514787/2000000000 : ℝ)*X 0 1+(1368537981/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5250924561/10000000000 : ℝ)*X 1 0+(-1220155301/10000000000 : ℝ)*X 1 1+(109483029/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5250924843/10000000000 : ℝ)*X 2 0+(2737075549/5000000000 : ℝ)*X 2 1+(-244031081/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2046972857/5000000000 : ℝ)*X 0 0+(923346219/2000000000 : ℝ)*X 0 1+(451323711/1250000000 : ℝ)*X 0 2+(2046972857/5000000000 : ℝ)*X 1 0+(923346219/2000000000 : ℝ)*X 1 1+(451323711/1250000000 : ℝ)*X 1 2+(2046972857/5000000000 : ℝ)*X 2 0+(923346219/2000000000 : ℝ)*X 2 1+(451323711/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3622315620497062519872418789/428250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202135997/25000000000000 : ℝ)*(base19) + (20461601/12500000000000 : ℝ)*(lower2) + (4070731/100000000000000 : ℝ)*(upper3) + (138066229/100000000000000 : ℝ)*(lower4) + (956781352782897/50000000000000 : ℝ)*(major0) + (956781352782897/50000000000000 : ℝ)*(major1) + (956781352782897/50000000000000 : ℝ)*(major2) + (114285627338679/4000000000000 : ℝ)*(sp0) + (1428571385095679/50000000000000 : ℝ)*(sp1) + (714284676865173/25000000000000 : ℝ)*(sp2) + (242495010236641/25000000000000 : ℝ)*(sp3) + (4404770927/100000000000000 : ℝ)*(sp4) + (377375639/25000000000000 : ℝ)*(sp5) + (638077721/10000000000000 : ℝ)*(sp6) + (242495010236641/25000000000000 : ℝ)*(f.failure) + (1428572544118951/50000000000000 : ℝ)*(f.sum) + (71283318530443/12847500000000000000000000000 : ℝ)*base65 + (148729767477931211/2569500000000000000000000000000000 : ℝ)*base67 + (4295352347174431211/2569500000000000000000000000000000 : ℝ)*base69 + (8500134186776068789/2569500000000000000000000000000000 : ℝ)*base72 + (8371548406753/12847500000000000000000000000 : ℝ)*base73 + (8305969133490931211/2569500000000000000000000000000000 : ℝ)*base75 + (3254942286479068789/2569500000000000000000000000000000 : ℝ)*base78 + (718045105065931211/2569500000000000000000000000000000 : ℝ)*base79 + (4279191703379/6423750000000000000000000000 : ℝ)*base81 + (619967/500000000000000000000 : ℝ)*base90 + (619967/500000000000000000000 : ℝ)*base92 + (619967/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (577915544385646623964643323/128475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (678769441/50000000000000 : ℝ)*(base19) + (185353859/10000000000000 : ℝ)*(base23) + (173196943/100000000000000 : ℝ)*(upper2) + (155193157/100000000000000 : ℝ)*(upper3) + (256500697/100000000000000 : ℝ)*(upper5) + (98037109369631/5000000000000 : ℝ)*(major0) + (98037109369631/5000000000000 : ℝ)*(major1) + (98037109369631/5000000000000 : ℝ)*(major2) + (9267825069/100000000000000 : ℝ)*(sp1) + (4884239983/50000000000000 : ℝ)*(sp2) + (292758902523377/10000000000000 : ℝ)*(sp4) + (146378919993491/5000000000000 : ℝ)*(sp5) + (1463788701607607/50000000000000 : ℝ)*(sp6) + (19877903992181/2000000000000 : ℝ)*(sp7) + (19877903992181/2000000000000 : ℝ)*(f.failure) + (292758902523377/10000000000000 : ℝ)*(f.sum) + (10348543782307/3854250000000000000000000000 : ℝ)*base65 + (2484138550587760559/770850000000000000000000000000000 : ℝ)*base67 + (5972500605084760559/770850000000000000000000000000000 : ℝ)*base69 + (83070499183660559/770850000000000000000000000000000 : ℝ)*base71 + (12697429534901/3854250000000000000000000000 : ℝ)*base74 + (4099510155098710559/770850000000000000000000000000000 : ℝ)*base75 + (6547468117045960559/770850000000000000000000000000000 : ℝ)*base77 + (2490472887126760559/770850000000000000000000000000000 : ℝ)*base79 + (1221166311503/1541700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (219947/40000000000000000000 : ℝ)*base90 + (219947/40000000000000000000 : ℝ)*base92 + (219947/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1717_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1/16 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (541/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1717_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1717_s2_0 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-693537963/5000000000 : ℝ)*x 0 + (5466005201/10000000000 : ℝ)*x 1 + (5138770409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (693537963/5000000000 : ℝ)^5359 ≤ (2174652514919/25000000000000 : ℝ)^4335 := by
    have hnat : (693537963 : ℕ)^5359*25000000000000^4335 ≤ 2174652514919^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693537963 5000000000 2174652514919 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466005201/10000000000 : ℝ)^5359 ≤ (47391809010431/100000000000000 : ℝ)^4335 := by
    have hnat : (5466005201 : ℕ)^5359*100000000000000^4335 ≤ 47391809010431^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466005201 10000000000 47391809010431 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138770409/10000000000 : ℝ)^5359 ≤ (43909580913109/100000000000000 : ℝ)^4335 := by
    have hnat : (5138770409 : ℕ)^5359*100000000000000^4335 ≤ 43909580913109^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138770409 10000000000 43909580913109 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-693537963/5000000000 : ℝ), (5466005201/10000000000 : ℝ), (5138770409/10000000000 : ℝ)] ![(2174652514919/25000000000000 : ℝ), (47391809010431/100000000000000 : ℝ), (43909580913109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-693537963/5000000000 : ℝ)|^5359 ≤ (2174652514919/25000000000000 : ℝ)^4335
        have hw : |(-693537963/5000000000 : ℝ)|=(693537963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466005201/10000000000 : ℝ)|^5359 ≤ (47391809010431/100000000000000 : ℝ)^4335
        have hw : |(5466005201/10000000000 : ℝ)|=(5466005201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138770409/10000000000 : ℝ)|^5359 ≤ (43909580913109/100000000000000 : ℝ)^4335
        have hw : |(5138770409/10000000000 : ℝ)|=(5138770409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s2_1 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670639749/5000000000 : ℝ)*x 0 + (-1556672341/10000000000 : ℝ)*x 1 + (6423463/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670639749/5000000000 : ℝ)^5359 ≤ (46058579405083/100000000000000 : ℝ)^4335 := by
    have hnat : (2670639749 : ℕ)^5359*100000000000000^4335 ≤ 46058579405083^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670639749 5000000000 46058579405083 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1556672341/10000000000 : ℝ)^5359 ≤ (31349499253/312500000000 : ℝ)^4335 := by
    have hnat : (1556672341 : ℕ)^5359*312500000000^4335 ≤ 31349499253^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556672341 10000000000 31349499253 312500000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6423463/12500000 : ℝ)^5359 ≤ (43909580818041/100000000000000 : ℝ)^4335 := by
    have hnat : (6423463 : ℕ)^5359*100000000000000^4335 ≤ 43909580818041^4335*12500000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6423463 12500000 43909580818041 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670639749/5000000000 : ℝ), (-1556672341/10000000000 : ℝ), (6423463/12500000 : ℝ)] ![(46058579405083/100000000000000 : ℝ), (31349499253/312500000000 : ℝ), (43909580818041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670639749/5000000000 : ℝ)|^5359 ≤ (46058579405083/100000000000000 : ℝ)^4335
        have hw : |(2670639749/5000000000 : ℝ)|=(2670639749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1556672341/10000000000 : ℝ)|^5359 ≤ (31349499253/312500000000 : ℝ)^4335
        have hw : |(-1556672341/10000000000 : ℝ)|=(1556672341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6423463/12500000 : ℝ)|^5359 ≤ (43909580818041/100000000000000 : ℝ)^4335
        have hw : |(6423463/12500000 : ℝ)|=(6423463/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s2_2 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341279343/10000000000 : ℝ)*x 0 + (5138770761/10000000000 : ℝ)*x 1 + (-1556672071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341279343/10000000000 : ℝ)^5359 ≤ (46058577752773/100000000000000 : ℝ)^4335 := by
    have hnat : (5341279343 : ℕ)^5359*100000000000000^4335 ≤ 46058577752773^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341279343 10000000000 46058577752773 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138770761/10000000000 : ℝ)^5359 ≤ (43909584631349/100000000000000 : ℝ)^4335 := by
    have hnat : (5138770761 : ℕ)^5359*100000000000000^4335 ≤ 43909584631349^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138770761 10000000000 43909584631349 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1556672071/10000000000 : ℝ)^5359 ≤ (10031837609953/100000000000000 : ℝ)^4335 := by
    have hnat : (1556672071 : ℕ)^5359*100000000000000^4335 ≤ 10031837609953^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556672071 10000000000 10031837609953 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341279343/10000000000 : ℝ), (5138770761/10000000000 : ℝ), (-1556672071/10000000000 : ℝ)] ![(46058577752773/100000000000000 : ℝ), (43909584631349/100000000000000 : ℝ), (10031837609953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341279343/10000000000 : ℝ)|^5359 ≤ (46058577752773/100000000000000 : ℝ)^4335
        have hw : |(5341279343/10000000000 : ℝ)|=(5341279343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138770761/10000000000 : ℝ)|^5359 ≤ (43909584631349/100000000000000 : ℝ)^4335
        have hw : |(5138770761/10000000000 : ℝ)|=(5138770761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1556672071/10000000000 : ℝ)|^5359 ≤ (10031837609953/100000000000000 : ℝ)^4335
        have hw : |(-1556672071/10000000000 : ℝ)|=(1556672071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s2_3 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1023936849/2500000000 : ℝ)*x 0 + (726282559/2000000000 : ℝ)*x 1 + (4595306197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023936849/2500000000 : ℝ)^5359 ≤ (2073193059479/6250000000000 : ℝ)^4335 := by
    have hnat : (1023936849 : ℕ)^5359*6250000000000^4335 ≤ 2073193059479^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023936849 2500000000 2073193059479 6250000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (726282559/2000000000 : ℝ)^5359 ≤ (1143452330309/4000000000000 : ℝ)^4335 := by
    have hnat : (726282559 : ℕ)^5359*4000000000000^4335 ≤ 1143452330309^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726282559 2000000000 1143452330309 4000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4595306197/10000000000 : ℝ)^5359 ≤ (7648520555891/20000000000000 : ℝ)^4335 := by
    have hnat : (4595306197 : ℕ)^5359*20000000000000^4335 ≤ 7648520555891^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595306197 10000000000 7648520555891 20000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1023936849/2500000000 : ℝ), (726282559/2000000000 : ℝ), (4595306197/10000000000 : ℝ)] ![(2073193059479/6250000000000 : ℝ), (1143452330309/4000000000000 : ℝ), (7648520555891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1023936849/2500000000 : ℝ)|^5359 ≤ (2073193059479/6250000000000 : ℝ)^4335
        have hw : |(1023936849/2500000000 : ℝ)|=(1023936849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(726282559/2000000000 : ℝ)|^5359 ≤ (1143452330309/4000000000000 : ℝ)^4335
        have hw : |(726282559/2000000000 : ℝ)|=(726282559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4595306197/10000000000 : ℝ)|^5359 ≤ (7648520555891/20000000000000 : ℝ)^4335
        have hw : |(4595306197/10000000000 : ℝ)|=(4595306197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s2_4 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1387223429/10000000000 : ℝ)*x 0 + (1285606267/2500000000 : ℝ)*x 1 + (5462296161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1387223429/10000000000 : ℝ)^5359 ≤ (2174938399413/25000000000000 : ℝ)^4335 := by
    have hnat : (1387223429 : ℕ)^5359*25000000000000^4335 ≤ 2174938399413^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387223429 10000000000 2174938399413 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285606267/2500000000 : ℝ)^5359 ≤ (43948188980753/100000000000000 : ℝ)^4335 := by
    have hnat : (1285606267 : ℕ)^5359*100000000000000^4335 ≤ 43948188980753^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285606267 2500000000 43948188980753 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462296161/10000000000 : ℝ)^5359 ≤ (23676028705629/50000000000000 : ℝ)^4335 := by
    have hnat : (5462296161 : ℕ)^5359*50000000000000^4335 ≤ 23676028705629^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462296161 10000000000 23676028705629 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1387223429/10000000000 : ℝ), (1285606267/2500000000 : ℝ), (5462296161/10000000000 : ℝ)] ![(2174938399413/25000000000000 : ℝ), (43948188980753/100000000000000 : ℝ), (23676028705629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1387223429/10000000000 : ℝ)|^5359 ≤ (2174938399413/25000000000000 : ℝ)^4335
        have hw : |(-1387223429/10000000000 : ℝ)|=(1387223429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285606267/2500000000 : ℝ)|^5359 ≤ (43948188980753/100000000000000 : ℝ)^4335
        have hw : |(1285606267/2500000000 : ℝ)|=(1285606267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462296161/10000000000 : ℝ)|^5359 ≤ (23676028705629/50000000000000 : ℝ)^4335
        have hw : |(5462296161/10000000000 : ℝ)|=(5462296161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s2_5 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656709883/1250000000 : ℝ)*x 0 + (-1233146747/10000000000 : ℝ)*x 1 + (2731148073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656709883/1250000000 : ℝ)^5359 ≤ (22563284742919/50000000000000 : ℝ)^4335 := by
    have hnat : (656709883 : ℕ)^5359*50000000000000^4335 ≤ 22563284742919^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656709883 1250000000 22563284742919 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1233146747/10000000000 : ℝ)^5359 ≤ (7521373251709/100000000000000 : ℝ)^4335 := by
    have hnat : (1233146747 : ℕ)^5359*100000000000000^4335 ≤ 7521373251709^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233146747 10000000000 7521373251709 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731148073/5000000000 : ℝ)^5359 ≤ (11838014312627/25000000000000 : ℝ)^4335 := by
    have hnat : (2731148073 : ℕ)^5359*25000000000000^4335 ≤ 11838014312627^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731148073 5000000000 11838014312627 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656709883/1250000000 : ℝ), (-1233146747/10000000000 : ℝ), (2731148073/5000000000 : ℝ)] ![(22563284742919/50000000000000 : ℝ), (7521373251709/100000000000000 : ℝ), (11838014312627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656709883/1250000000 : ℝ)|^5359 ≤ (22563284742919/50000000000000 : ℝ)^4335
        have hw : |(656709883/1250000000 : ℝ)|=(656709883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1233146747/10000000000 : ℝ)|^5359 ≤ (7521373251709/100000000000000 : ℝ)^4335
        have hw : |(-1233146747/10000000000 : ℝ)|=(1233146747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731148073/5000000000 : ℝ)|^5359 ≤ (11838014312627/25000000000000 : ℝ)^4335
        have hw : |(2731148073/5000000000 : ℝ)|=(2731148073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s2_6 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626839531/5000000000 : ℝ)*x 0 + (5462296137/10000000000 : ℝ)*x 1 + (-1233146763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626839531/5000000000 : ℝ)^5359 ≤ (45126569464601/100000000000000 : ℝ)^4335 := by
    have hnat : (2626839531 : ℕ)^5359*100000000000000^4335 ≤ 45126569464601^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626839531 5000000000 45126569464601 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462296137/10000000000 : ℝ)^5359 ≤ (47352057154059/100000000000000 : ℝ)^4335 := by
    have hnat : (5462296137 : ℕ)^5359*100000000000000^4335 ≤ 47352057154059^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462296137 10000000000 47352057154059 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233146763/10000000000 : ℝ)^5359 ≤ (150427467447/2000000000000 : ℝ)^4335 := by
    have hnat : (1233146763 : ℕ)^5359*2000000000000^4335 ≤ 150427467447^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233146763 10000000000 150427467447 2000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626839531/5000000000 : ℝ), (5462296137/10000000000 : ℝ), (-1233146763/10000000000 : ℝ)] ![(45126569464601/100000000000000 : ℝ), (47352057154059/100000000000000 : ℝ), (150427467447/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626839531/5000000000 : ℝ)|^5359 ≤ (45126569464601/100000000000000 : ℝ)^4335
        have hw : |(2626839531/5000000000 : ℝ)|=(2626839531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462296137/10000000000 : ℝ)|^5359 ≤ (47352057154059/100000000000000 : ℝ)^4335
        have hw : |(5462296137/10000000000 : ℝ)|=(5462296137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1233146763/10000000000 : ℝ)|^5359 ≤ (150427467447/2000000000000 : ℝ)^4335
        have hw : |(-1233146763/10000000000 : ℝ)|=(1233146763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s2_7 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (256011397/625000000 : ℝ)*x 0 + (4584541529/10000000000 : ℝ)*x 1 + (3642338497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256011397/625000000 : ℝ)^5359 ≤ (829386094739/2500000000000 : ℝ)^4335 := by
    have hnat : (256011397 : ℕ)^5359*2500000000000^4335 ≤ 829386094739^4335*625000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256011397 625000000 829386094739 2500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4584541529/10000000000 : ℝ)^5359 ≤ (38131887378559/100000000000000 : ℝ)^4335 := by
    have hnat : (4584541529 : ℕ)^5359*100000000000000^4335 ≤ 38131887378559^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584541529 10000000000 38131887378559 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3642338497/10000000000 : ℝ)^5359 ≤ (28692668823723/100000000000000 : ℝ)^4335 := by
    have hnat : (3642338497 : ℕ)^5359*100000000000000^4335 ≤ 28692668823723^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3642338497 10000000000 28692668823723 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(256011397/625000000 : ℝ), (4584541529/10000000000 : ℝ), (3642338497/10000000000 : ℝ)] ![(829386094739/2500000000000 : ℝ), (38131887378559/100000000000000 : ℝ), (28692668823723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(256011397/625000000 : ℝ)|^5359 ≤ (829386094739/2500000000000 : ℝ)^4335
        have hw : |(256011397/625000000 : ℝ)|=(256011397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4584541529/10000000000 : ℝ)|^5359 ≤ (38131887378559/100000000000000 : ℝ)^4335
        have hw : |(4584541529/10000000000 : ℝ)|=(4584541529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3642338497/10000000000 : ℝ)|^5359 ≤ (28692668823723/100000000000000 : ℝ)^4335
        have hw : |(3642338497/10000000000 : ℝ)|=(3642338497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1717_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (541/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10057/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (541/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (541/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (541/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (541/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (541/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (541/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9831/100000 : ℝ) ^ (5351/1024 : ℝ) ≤ (68020951133023/12500000000000000000 : ℝ) := by
    have hpowers : (9831/100000 : ℝ)^5351 ≤ (68020951133023/12500000000000000000 : ℝ)^1024 := by
      have hnat : (9831 : ℕ)^5351*12500000000000000000^1024 ≤ 68020951133023^1024*100000^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9831 100000 68020951133023 12500000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9831/100000 : ℝ)) (X := (68020951133023/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (541/3125 : ℝ) ^ (5351/1024 : ℝ) ≤ (10469310153845029/100000000000000000000 : ℝ) := by
    have hpowers : (541/3125 : ℝ)^5351 ≤ (10469310153845029/100000000000000000000 : ℝ)^1024 := by
      have hnat : (541 : ℕ)^5351*100000000000000000000^1024 ≤ 10469310153845029^1024*3125^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        541 3125 10469310153845029 100000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (541/3125 : ℝ)) (X := (10469310153845029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250068020951133023/6250000000000000000 : ℝ) ≤ (1250002603369369/1250000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (6250068020951133023/6250000000000000000 : ℝ)^1024 ≤ (1250002603369369/1250000000000000 : ℝ)^5351 := by
      have hnat : (6250068020951133023 : ℕ)^1024*1250000000000000^5351 ≤ 1250002603369369^5351*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250068020951133023 6250000000000000000 1250002603369369 1250000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002603369369/1250000000000000 : ℝ)) (X := (6250068020951133023/6250000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011013477762909213/100000000000000000000 : ℝ) ≤ (5000105375622027/5000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (100011013477762909213/100000000000000000000 : ℝ)^1024 ≤ (5000105375622027/5000000000000000 : ℝ)^5351 := by
      have hnat : (100011013477762909213 : ℕ)^1024*5000000000000000^5351 ≤ 5000105375622027^5351*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011013477762909213 100000000000000000000 5000105375622027 5000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000105375622027/5000000000000000 : ℝ)) (X := (100011013477762909213/100000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010469310153845029/50000000000000000000 : ℝ) ≤ (2500100168883289/2500000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50010469310153845029/50000000000000000000 : ℝ)^1024 ≤ (2500100168883289/2500000000000000 : ℝ)^5351 := by
      have hnat : (50010469310153845029 : ℕ)^1024*2500000000000000^5351 ≤ 2500100168883289^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010469310153845029 50000000000000000000 2500100168883289 2500000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500100168883289/2500000000000000 : ℝ)) (X := (50010469310153845029/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(68020951133023/12500000000000000000 : ℝ) ≤ ((18701605378769418097/18702500000000000000 : ℝ)+2*(94962144551/374050000000000 : ℝ)*(9831/100000 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (18701605378769418097/18702500000000000000 : ℝ)+2*(94962144551/374050000000000 : ℝ)*(9831/100000 : ℝ)=(1250002603369369/1250000000000000 : ℝ) by norm_num, show 1+2*(68020951133023/12500000000000000000 : ℝ)=(6250068020951133023/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10469310153845029/100000000000000000000 : ℝ)+(68020951133023/12500000000000000000 : ℝ) ≤ ((18701605378769418097/18702500000000000000 : ℝ)+(94962144551/374050000000000 : ℝ)*((541/3125 : ℝ)+(9831/100000 : ℝ)))^(5351/1024 : ℝ) := by
    rw [show (18701605378769418097/18702500000000000000 : ℝ)+(94962144551/374050000000000 : ℝ)*((541/3125 : ℝ)+(9831/100000 : ℝ))=(5000105375622027/5000000000000000 : ℝ) by norm_num, show 1+(10469310153845029/100000000000000000000 : ℝ)+(68020951133023/12500000000000000000 : ℝ)=(100011013477762909213/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10469310153845029/100000000000000000000 : ℝ) ≤ ((18701605378769418097/18702500000000000000 : ℝ)+2*(94962144551/374050000000000 : ℝ)*(541/3125 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (18701605378769418097/18702500000000000000 : ℝ)+2*(94962144551/374050000000000 : ℝ)*(541/3125 : ℝ)=(2500100168883289/2500000000000000 : ℝ) by norm_num, show 1+2*(10469310153845029/100000000000000000000 : ℝ)=(50010469310153845029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18701605378769418097/18702500000000000000 : ℝ)*(X 1 0+X 2 0)+(94962144551/374050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (18701605378769418097/18702500000000000000 : ℝ)) (alpha := (94962144551/374050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18701605378769418097/18702500000000000000 : ℝ)*(X 0 1+X 2 1)+(94962144551/374050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (18701605378769418097/18702500000000000000 : ℝ)) (alpha := (94962144551/374050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18701605378769418097/18702500000000000000 : ℝ)*(X 0 2+X 1 2)+(94962144551/374050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (9831/100000 : ℝ)) (hi := (541/3125 : ℝ)) (c := (18701605378769418097/18702500000000000000 : ℝ)) (alpha := (94962144551/374050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-693537963/5000000000 : ℝ)*X 0 0+(5466005201/10000000000 : ℝ)*X 0 1+(5138770409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2670639749/5000000000 : ℝ)*X 1 0+(-1556672341/10000000000 : ℝ)*X 1 1+(6423463/12500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5341279343/10000000000 : ℝ)*X 2 0+(5138770761/10000000000 : ℝ)*X 2 1+(-1556672071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1023936849/2500000000 : ℝ)*X 0 0+(726282559/2000000000 : ℝ)*X 0 1+(4595306197/10000000000 : ℝ)*X 0 2+(1023936849/2500000000 : ℝ)*X 1 0+(726282559/2000000000 : ℝ)*X 1 1+(4595306197/10000000000 : ℝ)*X 1 2+(1023936849/2500000000 : ℝ)*X 2 0+(726282559/2000000000 : ℝ)*X 2 1+(4595306197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1387223429/10000000000 : ℝ)*X 0 0+(1285606267/2500000000 : ℝ)*X 0 1+(5462296161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656709883/1250000000 : ℝ)*X 1 0+(-1233146747/10000000000 : ℝ)*X 1 1+(2731148073/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626839531/5000000000 : ℝ)*X 2 0+(5462296137/10000000000 : ℝ)*X 2 1+(-1233146763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((256011397/625000000 : ℝ)*X 0 0+(4584541529/10000000000 : ℝ)*X 0 1+(3642338497/10000000000 : ℝ)*X 0 2+(256011397/625000000 : ℝ)*X 1 0+(4584541529/10000000000 : ℝ)*X 1 1+(3642338497/10000000000 : ℝ)*X 1 2+(256011397/625000000 : ℝ)*X 2 0+(4584541529/10000000000 : ℝ)*X 2 1+(3642338497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1610200527970001501753979069/233781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1339878381/100000000000000 : ℝ)*(base19) + (243392009/20000000000000 : ℝ)*(base23) + (16313273/12500000000000 : ℝ)*(upper3) + (18287089/100000000000000 : ℝ)*(upper4) + (68033053/25000000000000 : ℝ)*(upper5) + (511675985432541/25000000000000 : ℝ)*(major0) + (511675985432541/25000000000000 : ℝ)*(major1) + (511675985432541/25000000000000 : ℝ)*(major2) + (305592264701761/10000000000000 : ℝ)*(sp0) + (1527968660491987/50000000000000 : ℝ)*(sp1) + (305593744390231/10000000000000 : ℝ)*(sp2) + (518732205267007/50000000000000 : ℝ)*(sp3) + (2001730593/12500000000000 : ℝ)*(sp4) + (4582476029/100000000000000 : ℝ)*(sp7) + (259367248252511/25000000000000 : ℝ)*(f.failure) + (611187732172471/20000000000000 : ℝ)*(f.sum) + (34198532781063/9351250000000000000000000000 : ℝ)*base66 + (5156308239890581977/467562500000000000000000000000000 : ℝ)*base67 + (3745880816869831977/467562500000000000000000000000000 : ℝ)*base69 + (4518627391547605523/467562500000000000000000000000000 : ℝ)*base72 + (270869848897243/37405000000000000000000000000 : ℝ)*base73 + (3701724529506956977/467562500000000000000000000000000 : ℝ)*base75 + (1806866482592480523/467562500000000000000000000000000 : ℝ)*base78 + (1245556713543831977/467562500000000000000000000000000 : ℝ)*base79 + (166108362805523/37405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5545343/500000000000000000000 : ℝ)*base89 + (5545343/500000000000000000000 : ℝ)*base91 + (5545343/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147398791024397559146258103/46756250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105502251/25000000000000 : ℝ)*(base19) + (223645049/50000000000000 : ℝ)*(base23) + (62601283/100000000000000 : ℝ)*(upper3) + (6892339/50000000000000 : ℝ)*(lower4) + (3403011/5000000000000 : ℝ)*(upper5) + (104690041806533/5000000000000 : ℝ)*(major0) + (104690041806533/5000000000000 : ℝ)*(major1) + (104690041806533/5000000000000 : ℝ)*(major2) + (3839092161/100000000000000 : ℝ)*(sp1) + (3853076987/100000000000000 : ℝ)*(sp2) + (1563129639430411/50000000000000 : ℝ)*(sp4) + (390781877219957/12500000000000 : ℝ)*(sp5) + (3126254978493737/100000000000000 : ℝ)*(sp6) + (212268457663473/20000000000000 : ℝ)*(sp7) + (212268457663473/20000000000000 : ℝ)*(f.failure) + (1563129639430411/50000000000000 : ℝ)*(f.sum) + (12612595134269/3740500000000000000000000000 : ℝ)*base66 + (68535398961415201/93512500000000000000000000000000 : ℝ)*base67 + (194387535743340201/93512500000000000000000000000000 : ℝ)*base69 + (483222264375347299/93512500000000000000000000000000 : ℝ)*base72 + (3213229617919/935125000000000000000000000 : ℝ)*base73 + (168255419933584799/93512500000000000000000000000000 : ℝ)*base76 + (542505175164259799/93512500000000000000000000000000 : ℝ)*base78 + (383642908933334799/93512500000000000000000000000000 : ℝ)*base80 + (28335005628907/7481000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1271249/400000000000000000000 : ℝ)*base89 + (1271249/400000000000000000000 : ℝ)*base91 + (1271249/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1717_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (541/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1717_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1717_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17051/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1717_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1717_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1717_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17051/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1717_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
