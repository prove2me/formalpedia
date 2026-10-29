-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1528_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:47.353999+00:00
-- url     : https://prove2.me/submissions/19bb4a16-0625-49ad-ba5e-acf48eb0da53

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
theorem support_rectangle_w1528_s3_0 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844222723/10000000000 : ℝ)*x 0 + (271694337/500000000 : ℝ)*x 1 + (521595149/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844222723/10000000000 : ℝ)^4553 ≤ (1129214639443/10000000000000 : ℝ)^3529 := by
    have hnat : (1844222723 : ℕ)^4553*10000000000000^3529 ≤ 1129214639443^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844222723 10000000000 1129214639443 10000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271694337/500000000 : ℝ)^4553 ≤ (45524833384683/100000000000000 : ℝ)^3529 := by
    have hnat : (271694337 : ℕ)^4553*100000000000000^3529 ≤ 45524833384683^3529*500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271694337 500000000 45524833384683 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521595149/1000000000 : ℝ)^4553 ≤ (43183020199607/100000000000000 : ℝ)^3529 := by
    have hnat : (521595149 : ℕ)^4553*100000000000000^3529 ≤ 43183020199607^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521595149 1000000000 43183020199607 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844222723/10000000000 : ℝ), (271694337/500000000 : ℝ), (521595149/1000000000 : ℝ)] ![(1129214639443/10000000000000 : ℝ), (45524833384683/100000000000000 : ℝ), (43183020199607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844222723/10000000000 : ℝ)|^4553 ≤ (1129214639443/10000000000000 : ℝ)^3529
        have hw : |(-1844222723/10000000000 : ℝ)|=(1844222723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271694337/500000000 : ℝ)|^4553 ≤ (45524833384683/100000000000000 : ℝ)^3529
        have hw : |(271694337/500000000 : ℝ)|=(271694337/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521595149/1000000000 : ℝ)|^4553 ≤ (43183020199607/100000000000000 : ℝ)^3529
        have hw : |(521595149/1000000000 : ℝ)|=(521595149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s3_1 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334462709/625000000 : ℝ)*x 0 + (-488966711/2500000000 : ℝ)*x 1 + (2607975691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334462709/625000000 : ℝ)^4553 ≤ (44635244502859/100000000000000 : ℝ)^3529 := by
    have hnat : (334462709 : ℕ)^4553*100000000000000^3529 ≤ 44635244502859^3529*625000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334462709 625000000 44635244502859 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488966711/2500000000 : ℝ)^4553 ≤ (12181736434221/100000000000000 : ℝ)^3529 := by
    have hnat : (488966711 : ℕ)^4553*100000000000000^3529 ≤ 12181736434221^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488966711 2500000000 12181736434221 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607975691/5000000000 : ℝ)^4553 ≤ (43183019046023/100000000000000 : ℝ)^3529 := by
    have hnat : (2607975691 : ℕ)^4553*100000000000000^3529 ≤ 43183019046023^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607975691 5000000000 43183019046023 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334462709/625000000 : ℝ), (-488966711/2500000000 : ℝ), (2607975691/5000000000 : ℝ)] ![(44635244502859/100000000000000 : ℝ), (12181736434221/100000000000000 : ℝ), (43183019046023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334462709/625000000 : ℝ)|^4553 ≤ (44635244502859/100000000000000 : ℝ)^3529
        have hw : |(334462709/625000000 : ℝ)|=(334462709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-488966711/2500000000 : ℝ)|^4553 ≤ (12181736434221/100000000000000 : ℝ)^3529
        have hw : |(-488966711/2500000000 : ℝ)|=(488966711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607975691/5000000000 : ℝ)|^4553 ≤ (43183019046023/100000000000000 : ℝ)^3529
        have hw : |(2607975691/5000000000 : ℝ)|=(2607975691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s3_2 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070280703/2000000000 : ℝ)*x 0 + (1303987789/2500000000 : ℝ)*x 1 + (-391173383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070280703/2000000000 : ℝ)^4553 ≤ (8927049268601/20000000000000 : ℝ)^3529 := by
    have hnat : (1070280703 : ℕ)^4553*20000000000000^3529 ≤ 8927049268601^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070280703 2000000000 8927049268601 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303987789/2500000000 : ℝ)^4553 ≤ (21591508316021/50000000000000 : ℝ)^3529 := by
    have hnat : (1303987789 : ℕ)^4553*50000000000000^3529 ≤ 21591508316021^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303987789 2500000000 21591508316021 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391173383/2000000000 : ℝ)^4553 ≤ (6090868502373/50000000000000 : ℝ)^3529 := by
    have hnat : (391173383 : ℕ)^4553*50000000000000^3529 ≤ 6090868502373^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391173383 2000000000 6090868502373 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070280703/2000000000 : ℝ), (1303987789/2500000000 : ℝ), (-391173383/2000000000 : ℝ)] ![(8927049268601/20000000000000 : ℝ), (21591508316021/50000000000000 : ℝ), (6090868502373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070280703/2000000000 : ℝ)|^4553 ≤ (8927049268601/20000000000000 : ℝ)^3529
        have hw : |(1070280703/2000000000 : ℝ)|=(1070280703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303987789/2500000000 : ℝ)|^4553 ≤ (21591508316021/50000000000000 : ℝ)^3529
        have hw : |(1303987789/2500000000 : ℝ)|=(1303987789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391173383/2000000000 : ℝ)|^4553 ≤ (6090868502373/50000000000000 : ℝ)^3529
        have hw : |(-391173383/2000000000 : ℝ)|=(391173383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s3_3 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852424017/2000000000 : ℝ)*x 0 + (1004593787/2500000000 : ℝ)*x 1 + (4518139227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852424017/2000000000 : ℝ)^4553 ≤ (207986537691/625000000000 : ℝ)^3529 := by
    have hnat : (852424017 : ℕ)^4553*625000000000^3529 ≤ 207986537691^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852424017 2000000000 207986537691 625000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004593787/2500000000 : ℝ)^4553 ≤ (6168632768777/20000000000000 : ℝ)^3529 := by
    have hnat : (1004593787 : ℕ)^4553*20000000000000^3529 ≤ 6168632768777^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004593787 2500000000 6168632768777 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518139227/10000000000 : ℝ)^4553 ≤ (17939495056183/50000000000000 : ℝ)^3529 := by
    have hnat : (4518139227 : ℕ)^4553*50000000000000^3529 ≤ 17939495056183^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518139227 10000000000 17939495056183 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852424017/2000000000 : ℝ), (1004593787/2500000000 : ℝ), (4518139227/10000000000 : ℝ)] ![(207986537691/625000000000 : ℝ), (6168632768777/20000000000000 : ℝ), (17939495056183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852424017/2000000000 : ℝ)|^4553 ≤ (207986537691/625000000000 : ℝ)^3529
        have hw : |(852424017/2000000000 : ℝ)|=(852424017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004593787/2500000000 : ℝ)|^4553 ≤ (6168632768777/20000000000000 : ℝ)^3529
        have hw : |(1004593787/2500000000 : ℝ)|=(1004593787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4518139227/10000000000 : ℝ)|^4553 ≤ (17939495056183/50000000000000 : ℝ)^3529
        have hw : |(4518139227/10000000000 : ℝ)|=(4518139227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s3_4 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844253253/10000000000 : ℝ)*x 0 + (5217103969/10000000000 : ℝ)*x 1 + (1358181371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844253253/10000000000 : ℝ)^4553 ≤ (11292387572031/100000000000000 : ℝ)^3529 := by
    have hnat : (1844253253 : ℕ)^4553*100000000000000^3529 ≤ 11292387572031^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844253253 10000000000 11292387572031 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217103969/10000000000 : ℝ)^4553 ≤ (21597665303187/50000000000000 : ℝ)^3529 := by
    have hnat : (5217103969 : ℕ)^4553*50000000000000^3529 ≤ 21597665303187^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217103969 10000000000 21597665303187 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358181371/2500000000 : ℝ)^4553 ≤ (22756140904061/50000000000000 : ℝ)^3529 := by
    have hnat : (1358181371 : ℕ)^4553*50000000000000^3529 ≤ 22756140904061^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358181371 2500000000 22756140904061 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844253253/10000000000 : ℝ), (5217103969/10000000000 : ℝ), (1358181371/2500000000 : ℝ)] ![(11292387572031/100000000000000 : ℝ), (21597665303187/50000000000000 : ℝ), (22756140904061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844253253/10000000000 : ℝ)|^4553 ≤ (11292387572031/100000000000000 : ℝ)^3529
        have hw : |(-1844253253/10000000000 : ℝ)|=(1844253253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217103969/10000000000 : ℝ)|^4553 ≤ (21597665303187/50000000000000 : ℝ)^3529
        have hw : |(5217103969/10000000000 : ℝ)|=(5217103969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358181371/2500000000 : ℝ)|^4553 ≤ (22756140904061/50000000000000 : ℝ)^3529
        have hw : |(1358181371/2500000000 : ℝ)|=(1358181371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s3_5 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66175717/125000000 : ℝ)*x 0 + (-217386579/1250000000 : ℝ)*x 1 + (1358181381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66175717/125000000 : ℝ)^4553 ≤ (4401910113661/10000000000000 : ℝ)^3529 := by
    have hnat : (66175717 : ℕ)^4553*10000000000000^3529 ≤ 4401910113661^3529*125000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66175717 125000000 4401910113661 10000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217386579/1250000000 : ℝ)^4553 ≤ (10468616608861/100000000000000 : ℝ)^3529 := by
    have hnat : (217386579 : ℕ)^4553*100000000000000^3529 ≤ 10468616608861^3529*1250000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217386579 1250000000 10468616608861 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358181381/2500000000 : ℝ)^4553 ≤ (45512282240453/100000000000000 : ℝ)^3529 := by
    have hnat : (1358181381 : ℕ)^4553*100000000000000^3529 ≤ 45512282240453^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358181381 2500000000 45512282240453 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66175717/125000000 : ℝ), (-217386579/1250000000 : ℝ), (1358181381/2500000000 : ℝ)] ![(4401910113661/10000000000000 : ℝ), (10468616608861/100000000000000 : ℝ), (45512282240453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66175717/125000000 : ℝ)|^4553 ≤ (4401910113661/10000000000000 : ℝ)^3529
        have hw : |(66175717/125000000 : ℝ)|=(66175717/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217386579/1250000000 : ℝ)|^4553 ≤ (10468616608861/100000000000000 : ℝ)^3529
        have hw : |(-217386579/1250000000 : ℝ)|=(217386579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358181381/2500000000 : ℝ)|^4553 ≤ (45512282240453/100000000000000 : ℝ)^3529
        have hw : |(1358181381/2500000000 : ℝ)|=(1358181381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s3_6 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294057553/10000000000 : ℝ)*x 0 + (2716362679/5000000000 : ℝ)*x 1 + (-434773149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294057553/10000000000 : ℝ)^4553 ≤ (44019103207017/100000000000000 : ℝ)^3529 := by
    have hnat : (5294057553 : ℕ)^4553*100000000000000^3529 ≤ 44019103207017^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294057553 10000000000 44019103207017 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716362679/5000000000 : ℝ)^4553 ≤ (22756140223139/50000000000000 : ℝ)^3529 := by
    have hnat : (2716362679 : ℕ)^4553*50000000000000^3529 ≤ 22756140223139^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716362679 5000000000 22756140223139 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434773149/2500000000 : ℝ)^4553 ≤ (418744653171/4000000000000 : ℝ)^3529 := by
    have hnat : (434773149 : ℕ)^4553*4000000000000^3529 ≤ 418744653171^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434773149 2500000000 418744653171 4000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294057553/10000000000 : ℝ), (2716362679/5000000000 : ℝ), (-434773149/2500000000 : ℝ)] ![(44019103207017/100000000000000 : ℝ), (22756140223139/50000000000000 : ℝ), (418744653171/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294057553/10000000000 : ℝ)|^4553 ≤ (44019103207017/100000000000000 : ℝ)^3529
        have hw : |(5294057553/10000000000 : ℝ)|=(5294057553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716362679/5000000000 : ℝ)|^4553 ≤ (22756140223139/50000000000000 : ℝ)^3529
        have hw : |(2716362679/5000000000 : ℝ)|=(2716362679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434773149/2500000000 : ℝ)|^4553 ≤ (418744653171/4000000000000 : ℝ)^3529
        have hw : |(-434773149/2500000000 : ℝ)|=(434773149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s3_7 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4262190123/10000000000 : ℝ)*x 0 + (4515495961/10000000000 : ℝ)*x 1 + (804207627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4262190123/10000000000 : ℝ)^4553 ≤ (33278551552119/100000000000000 : ℝ)^3529 := by
    have hnat : (4262190123 : ℕ)^4553*100000000000000^3529 ≤ 33278551552119^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262190123 10000000000 33278551552119 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515495961/10000000000 : ℝ)^4553 ≤ (35851911238869/100000000000000 : ℝ)^3529 := by
    have hnat : (4515495961 : ℕ)^4553*100000000000000^3529 ≤ 35851911238869^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515495961 10000000000 35851911238869 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804207627/2000000000 : ℝ)^4553 ≤ (30869537189593/100000000000000 : ℝ)^3529 := by
    have hnat : (804207627 : ℕ)^4553*100000000000000^3529 ≤ 30869537189593^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804207627 2000000000 30869537189593 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4262190123/10000000000 : ℝ), (4515495961/10000000000 : ℝ), (804207627/2000000000 : ℝ)] ![(33278551552119/100000000000000 : ℝ), (35851911238869/100000000000000 : ℝ), (30869537189593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4262190123/10000000000 : ℝ)|^4553 ≤ (33278551552119/100000000000000 : ℝ)^3529
        have hw : |(4262190123/10000000000 : ℝ)|=(4262190123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515495961/10000000000 : ℝ)|^4553 ≤ (35851911238869/100000000000000 : ℝ)^3529
        have hw : |(4515495961/10000000000 : ℝ)|=(4515495961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(804207627/2000000000 : ℝ)|^4553 ≤ (30869537189593/100000000000000 : ℝ)^3529
        have hw : |(804207627/2000000000 : ℝ)|=(804207627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1528_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15939/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5279/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2731/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15541/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15939/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5279/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15939/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5279/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15939/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5279/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15939/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5279/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15939/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5279/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15939/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5279/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5279/50000 : ℝ) ^ (4551/1024 : ℝ) ≤ (571977419581171/12500000000000000000 : ℝ) := by
    have hpowers : (5279/50000 : ℝ)^4551 ≤ (571977419581171/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5279 : ℕ)^4551*12500000000000000000^1024 ≤ 571977419581171^1024*50000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5279 50000 571977419581171 12500000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5279/50000 : ℝ)) (X := (571977419581171/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15939/100000 : ℝ) ^ (4551/1024 : ℝ) ≤ (28540992710900129/100000000000000000000 : ℝ) := by
    have hpowers : (15939/100000 : ℝ)^4551 ≤ (28540992710900129/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15939 : ℕ)^4551*100000000000000000000^1024 ≤ 28540992710900129^1024*100000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15939 100000 28540992710900129 100000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15939/100000 : ℝ)) (X := (28540992710900129/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250571977419581171/6250000000000000000 : ℝ) ≤ (39063304334361/39062500000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (6250571977419581171/6250000000000000000 : ℝ)^1024 ≤ (39063304334361/39062500000000 : ℝ)^4551 := by
      have hnat : (6250571977419581171 : ℕ)^1024*39062500000000^4551 ≤ 39063304334361^4551*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250571977419581171 6250000000000000000 39063304334361 39062500000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39063304334361/39062500000000 : ℝ)) (X := (6250571977419581171/6250000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033116812067549497/100000000000000000000 : ℝ) ≤ (1000074505086009/1000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (100033116812067549497/100000000000000000000 : ℝ)^1024 ≤ (1000074505086009/1000000000000000 : ℝ)^4551 := by
      have hnat : (100033116812067549497 : ℕ)^1024*1000000000000000^4551 ≤ 1000074505086009^4551*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033116812067549497 100000000000000000000 1000074505086009 1000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000074505086009/1000000000000000 : ℝ)) (X := (100033116812067549497/100000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028540992710900129/50000000000000000000 : ℝ) ≤ (2500321048030941/2500000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (50028540992710900129/50000000000000000000 : ℝ)^1024 ≤ (2500321048030941/2500000000000000 : ℝ)^4551 := by
      have hnat : (50028540992710900129 : ℕ)^1024*2500000000000000^4551 ≤ 2500321048030941^4551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028540992710900129 50000000000000000000 2500321048030941 2500000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500321048030941/2500000000000000 : ℝ)) (X := (50028540992710900129/50000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(571977419581171/12500000000000000000 : ℝ) ≤ ((6724965436576821789/6726250000000000000 : ℝ)+2*(269570631837/269050000000000 : ℝ)*(5279/50000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (6724965436576821789/6726250000000000000 : ℝ)+2*(269570631837/269050000000000 : ℝ)*(5279/50000 : ℝ)=(39063304334361/39062500000000 : ℝ) by norm_num, show 1+2*(571977419581171/12500000000000000000 : ℝ)=(6250571977419581171/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28540992710900129/100000000000000000000 : ℝ)+(571977419581171/12500000000000000000 : ℝ) ≤ ((6724965436576821789/6726250000000000000 : ℝ)+(269570631837/269050000000000 : ℝ)*((15939/100000 : ℝ)+(5279/50000 : ℝ)))^(4551/1024 : ℝ) := by
    rw [show (6724965436576821789/6726250000000000000 : ℝ)+(269570631837/269050000000000 : ℝ)*((15939/100000 : ℝ)+(5279/50000 : ℝ))=(1000074505086009/1000000000000000 : ℝ) by norm_num, show 1+(28540992710900129/100000000000000000000 : ℝ)+(571977419581171/12500000000000000000 : ℝ)=(100033116812067549497/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28540992710900129/100000000000000000000 : ℝ) ≤ ((6724965436576821789/6726250000000000000 : ℝ)+2*(269570631837/269050000000000 : ℝ)*(15939/100000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (6724965436576821789/6726250000000000000 : ℝ)+2*(269570631837/269050000000000 : ℝ)*(15939/100000 : ℝ)=(2500321048030941/2500000000000000 : ℝ) by norm_num, show 1+2*(28540992710900129/100000000000000000000 : ℝ)=(50028540992710900129/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6724965436576821789/6726250000000000000 : ℝ)*(X 1 0+X 2 0)+(269570631837/269050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (5279/50000 : ℝ)) (hi := (15939/100000 : ℝ)) (c := (6724965436576821789/6726250000000000000 : ℝ)) (alpha := (269570631837/269050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6724965436576821789/6726250000000000000 : ℝ)*(X 0 1+X 2 1)+(269570631837/269050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (5279/50000 : ℝ)) (hi := (15939/100000 : ℝ)) (c := (6724965436576821789/6726250000000000000 : ℝ)) (alpha := (269570631837/269050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6724965436576821789/6726250000000000000 : ℝ)*(X 0 2+X 1 2)+(269570631837/269050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (5279/50000 : ℝ)) (hi := (15939/100000 : ℝ)) (c := (6724965436576821789/6726250000000000000 : ℝ)) (alpha := (269570631837/269050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1844222723/10000000000 : ℝ)*X 0 0+(271694337/500000000 : ℝ)*X 0 1+(521595149/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334462709/625000000 : ℝ)*X 1 0+(-488966711/2500000000 : ℝ)*X 1 1+(2607975691/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070280703/2000000000 : ℝ)*X 2 0+(1303987789/2500000000 : ℝ)*X 2 1+(-391173383/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((852424017/2000000000 : ℝ)*X 0 0+(1004593787/2500000000 : ℝ)*X 0 1+(4518139227/10000000000 : ℝ)*X 0 2+(852424017/2000000000 : ℝ)*X 1 0+(1004593787/2500000000 : ℝ)*X 1 1+(4518139227/10000000000 : ℝ)*X 1 2+(852424017/2000000000 : ℝ)*X 2 0+(1004593787/2500000000 : ℝ)*X 2 1+(4518139227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1844253253/10000000000 : ℝ)*X 0 0+(5217103969/10000000000 : ℝ)*X 0 1+(1358181371/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66175717/125000000 : ℝ)*X 1 0+(-217386579/1250000000 : ℝ)*X 1 1+(1358181381/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294057553/10000000000 : ℝ)*X 2 0+(2716362679/5000000000 : ℝ)*X 2 1+(-434773149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4262190123/10000000000 : ℝ)*X 0 0+(4515495961/10000000000 : ℝ)*X 0 1+(804207627/2000000000 : ℝ)*X 0 2+(4262190123/10000000000 : ℝ)*X 1 0+(4515495961/10000000000 : ℝ)*X 1 1+(804207627/2000000000 : ℝ)*X 1 2+(4262190123/10000000000 : ℝ)*X 2 0+(4515495961/10000000000 : ℝ)*X 2 1+(804207627/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81504829007569048388517177/16815625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (528213113/100000000000000 : ℝ)*(base19) + (157589543/25000000000000 : ℝ)*(base23) + (34797019/50000000000000 : ℝ)*(lower2) + (77231357/100000000000000 : ℝ)*(upper3) + (22896051/50000000000000 : ℝ)*(lower4) + (329474175619931/10000000000000 : ℝ)*(major0) + (329474175619931/10000000000000 : ℝ)*(major1) + (329474175619931/10000000000000 : ℝ)*(major2) + (4588525612082757/100000000000000 : ℝ)*(sp0) + (4588530892325839/100000000000000 : ℝ)*(sp1) + (4588530790180781/100000000000000 : ℝ)*(sp2) + (100047367950199/5000000000000 : ℝ)*(sp3) + (1452114049/25000000000000 : ℝ)*(sp4) + (4571290017/100000000000000 : ℝ)*(sp7) + (2000951930293997/100000000000000 : ℝ)*(f.failure) + (4588531420538953/100000000000000 : ℝ)*(f.sum) + (1519762739817/672625000000000000000000000 : ℝ)*base65 + (516097509163610941/67262500000000000000000000000000 : ℝ)*base68 + (154183830037460941/67262500000000000000000000000000 : ℝ)*base70 + (206390793681185941/67262500000000000000000000000000 : ℝ)*base72 + (2164402299453/5381000000000000000000000000 : ℝ)*base74 + (112040963084739059/67262500000000000000000000000000 : ℝ)*base75 + (217599389708923441/67262500000000000000000000000000 : ℝ)*base78 + (996805695749760941/67262500000000000000000000000000 : ℝ)*base80 + (591396534831/672625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (12131963/2500000000000000000000 : ℝ)*base89 + (12131963/2500000000000000000000 : ℝ)*base91 + (12131963/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (934760698930276291582841301/84078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214206873/12500000000000 : ℝ)*(base19) + (225369179/10000000000000 : ℝ)*(base23) + (221756997/100000000000000 : ℝ)*(upper3) + (160379119/100000000000000 : ℝ)*(lower4) + (211160277/100000000000000 : ℝ)*(upper5) + (832521414273739/25000000000000 : ℝ)*(major0) + (832521414273739/25000000000000 : ℝ)*(major1) + (832521414273739/25000000000000 : ℝ)*(major2) + (5346276827/20000000000000 : ℝ)*(sp1) + (33010974147/100000000000000 : ℝ)*(sp2) + (2318877034738401/50000000000000 : ℝ)*(sp4) + (1159431406109421/25000000000000 : ℝ)*(sp5) + (289857425300679/6250000000000 : ℝ)*(sp6) + (2022416874120989/100000000000000 : ℝ)*(sp7) + (2022416874120989/100000000000000 : ℝ)*(f.failure) + (2318877034738401/50000000000000 : ℝ)*(f.sum) + (40147767621739/26905000000000000000000000000 : ℝ)*base65 + (546745727115319679/168156250000000000000000000000000 : ℝ)*base68 + (2105703002402694679/168156250000000000000000000000000 : ℝ)*base70 + (722929884289069679/168156250000000000000000000000000 : ℝ)*base72 + (81395649315439/26905000000000000000000000000 : ℝ)*base73 + (3277440777079507179/168156250000000000000000000000000 : ℝ)*base76 + (202521263327274071/168156250000000000000000000000000 : ℝ)*base77 + (632476173252382179/168156250000000000000000000000000 : ℝ)*base80 + (101620812138693/13452500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (19347531/2500000000000000000000 : ℝ)*base89 + (19347531/2500000000000000000000 : ℝ)*base91 + (19347531/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1528_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15939/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5279/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15541/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1528_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1528_s4_0 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844588577/10000000000 : ℝ)*x 0 + (678934213/1250000000 : ℝ)*x 1 + (1304530621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844588577/10000000000 : ℝ)^4553 ≤ (11295036604631/100000000000000 : ℝ)^3529 := by
    have hnat : (1844588577 : ℕ)^4553*100000000000000^3529 ≤ 11295036604631^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844588577 10000000000 11295036604631 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678934213/1250000000 : ℝ)^4553 ≤ (45498752663777/100000000000000 : ℝ)^3529 := by
    have hnat : (678934213 : ℕ)^4553*100000000000000^3529 ≤ 45498752663777^3529*1250000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678934213 1250000000 45498752663777 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304530621/2500000000 : ℝ)^4553 ≤ (43206210710013/100000000000000 : ℝ)^3529 := by
    have hnat : (1304530621 : ℕ)^4553*100000000000000^3529 ≤ 43206210710013^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304530621 2500000000 43206210710013 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844588577/10000000000 : ℝ), (678934213/1250000000 : ℝ), (1304530621/2500000000 : ℝ)] ![(11295036604631/100000000000000 : ℝ), (45498752663777/100000000000000 : ℝ), (43206210710013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844588577/10000000000 : ℝ)|^4553 ≤ (11295036604631/100000000000000 : ℝ)^3529
        have hw : |(-1844588577/10000000000 : ℝ)|=(1844588577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678934213/1250000000 : ℝ)|^4553 ≤ (45498752663777/100000000000000 : ℝ)^3529
        have hw : |(678934213/1250000000 : ℝ)|=(678934213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304530621/2500000000 : ℝ)|^4553 ≤ (43206210710013/100000000000000 : ℝ)^3529
        have hw : |(1304530621/2500000000 : ℝ)|=(1304530621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s4_1 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675384683/5000000000 : ℝ)*x 0 + (-976914559/5000000000 : ℝ)*x 1 + (5218122699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675384683/5000000000 : ℝ)^4553 ≤ (5578552790803/12500000000000 : ℝ)^3529 := by
    have hnat : (2675384683 : ℕ)^4553*12500000000000^3529 ≤ 5578552790803^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675384683 5000000000 5578552790803 12500000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976914559/5000000000 : ℝ)^4553 ≤ (2433072929897/20000000000000 : ℝ)^3529 := by
    have hnat : (976914559 : ℕ)^4553*20000000000000^3529 ≤ 2433072929897^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976914559 5000000000 2433072929897 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218122699/10000000000 : ℝ)^4553 ≤ (43206213006777/100000000000000 : ℝ)^3529 := by
    have hnat : (5218122699 : ℕ)^4553*100000000000000^3529 ≤ 43206213006777^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218122699 10000000000 43206213006777 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675384683/5000000000 : ℝ), (-976914559/5000000000 : ℝ), (5218122699/10000000000 : ℝ)] ![(5578552790803/12500000000000 : ℝ), (2433072929897/20000000000000 : ℝ), (43206213006777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675384683/5000000000 : ℝ)|^4553 ≤ (5578552790803/12500000000000 : ℝ)^3529
        have hw : |(2675384683/5000000000 : ℝ)|=(2675384683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976914559/5000000000 : ℝ)|^4553 ≤ (2433072929897/20000000000000 : ℝ)^3529
        have hw : |(-976914559/5000000000 : ℝ)|=(976914559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218122699/10000000000 : ℝ)|^4553 ≤ (43206213006777/100000000000000 : ℝ)^3529
        have hw : |(5218122699/10000000000 : ℝ)|=(5218122699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s4_2 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668846211/1250000000 : ℝ)*x 0 + (1043624479/2000000000 : ℝ)*x 1 + (-1953829091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668846211/1250000000 : ℝ)^4553 ≤ (2789276611961/6250000000000 : ℝ)^3529 := by
    have hnat : (668846211 : ℕ)^4553*6250000000000^3529 ≤ 2789276611961^3529*1250000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668846211 1250000000 2789276611961 6250000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043624479/2000000000 : ℝ)^4553 ≤ (2160310487963/5000000000000 : ℝ)^3529 := by
    have hnat : (1043624479 : ℕ)^4553*5000000000000^3529 ≤ 2160310487963^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043624479 2000000000 2160310487963 5000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1953829091/10000000000 : ℝ)^4553 ≤ (12165364432591/100000000000000 : ℝ)^3529 := by
    have hnat : (1953829091 : ℕ)^4553*100000000000000^3529 ≤ 12165364432591^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953829091 10000000000 12165364432591 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668846211/1250000000 : ℝ), (1043624479/2000000000 : ℝ), (-1953829091/10000000000 : ℝ)] ![(2789276611961/6250000000000 : ℝ), (2160310487963/5000000000000 : ℝ), (12165364432591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668846211/1250000000 : ℝ)|^4553 ≤ (2789276611961/6250000000000 : ℝ)^3529
        have hw : |(668846211/1250000000 : ℝ)|=(668846211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043624479/2000000000 : ℝ)|^4553 ≤ (2160310487963/5000000000000 : ℝ)^3529
        have hw : |(1043624479/2000000000 : ℝ)|=(1043624479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1953829091/10000000000 : ℝ)|^4553 ≤ (12165364432591/100000000000000 : ℝ)^3529
        have hw : |(-1953829091/10000000000 : ℝ)|=(1953829091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s4_3 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34098797/80000000 : ℝ)*x 0 + (4023605021/10000000000 : ℝ)*x 1 + (564107089/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34098797/80000000 : ℝ)^4553 ≤ (16640079146937/50000000000000 : ℝ)^3529 := by
    have hnat : (34098797 : ℕ)^4553*50000000000000^3529 ≤ 16640079146937^3529*80000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34098797 80000000 16640079146937 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023605021/10000000000 : ℝ)^4553 ≤ (154474817901/500000000000 : ℝ)^3529 := by
    have hnat : (4023605021 : ℕ)^4553*500000000000^3529 ≤ 154474817901^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023605021 10000000000 154474817901 500000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564107089/1250000000 : ℝ)^4553 ≤ (17912439053049/50000000000000 : ℝ)^3529 := by
    have hnat : (564107089 : ℕ)^4553*50000000000000^3529 ≤ 17912439053049^3529*1250000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564107089 1250000000 17912439053049 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34098797/80000000 : ℝ), (4023605021/10000000000 : ℝ), (564107089/1250000000 : ℝ)] ![(16640079146937/50000000000000 : ℝ), (154474817901/500000000000 : ℝ), (17912439053049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34098797/80000000 : ℝ)|^4553 ≤ (16640079146937/50000000000000 : ℝ)^3529
        have hw : |(34098797/80000000 : ℝ)|=(34098797/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023605021/10000000000 : ℝ)|^4553 ≤ (154474817901/500000000000 : ℝ)^3529
        have hw : |(4023605021/10000000000 : ℝ)|=(4023605021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564107089/1250000000 : ℝ)|^4553 ≤ (17912439053049/50000000000000 : ℝ)^3529
        have hw : |(564107089/1250000000 : ℝ)|=(564107089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s4_4 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-36892339/200000000 : ℝ)*x 0 + (5219227287/10000000000 : ℝ)*x 1 + (5430360867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36892339/200000000 : ℝ)^4553 ≤ (11295260755459/100000000000000 : ℝ)^3529 := by
    have hnat : (36892339 : ℕ)^4553*100000000000000^3529 ≤ 11295260755459^3529*200000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36892339 200000000 11295260755459 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219227287/10000000000 : ℝ)^4553 ≤ (10804503316619/25000000000000 : ℝ)^3529 := by
    have hnat : (5219227287 : ℕ)^4553*25000000000000^3529 ≤ 10804503316619^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219227287 10000000000 10804503316619 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430360867/10000000000 : ℝ)^4553 ≤ (11371681491153/25000000000000 : ℝ)^3529 := by
    have hnat : (5430360867 : ℕ)^4553*25000000000000^3529 ≤ 11371681491153^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430360867 10000000000 11371681491153 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36892339/200000000 : ℝ), (5219227287/10000000000 : ℝ), (5430360867/10000000000 : ℝ)] ![(11295260755459/100000000000000 : ℝ), (10804503316619/25000000000000 : ℝ), (11371681491153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36892339/200000000 : ℝ)|^4553 ≤ (11295260755459/100000000000000 : ℝ)^3529
        have hw : |(-36892339/200000000 : ℝ)|=(36892339/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219227287/10000000000 : ℝ)|^4553 ≤ (10804503316619/25000000000000 : ℝ)^3529
        have hw : |(5219227287/10000000000 : ℝ)|=(5219227287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430360867/10000000000 : ℝ)|^4553 ≤ (11371681491153/25000000000000 : ℝ)^3529
        have hw : |(5430360867/10000000000 : ℝ)|=(5430360867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s4_5 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323657711/2500000000 : ℝ)*x 0 + (-27212353/156250000 : ℝ)*x 1 + (543036089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323657711/2500000000 : ℝ)^4553 ≤ (44025253282853/100000000000000 : ℝ)^3529 := by
    have hnat : (1323657711 : ℕ)^4553*100000000000000^3529 ≤ 44025253282853^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323657711 2500000000 44025253282853 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27212353/156250000 : ℝ)^4553 ≤ (1311002560743/12500000000000 : ℝ)^3529 := by
    have hnat : (27212353 : ℕ)^4553*12500000000000^3529 ≤ 1311002560743^3529*156250000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27212353 156250000 1311002560743 12500000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543036089/1000000000 : ℝ)^4553 ≤ (45486726213171/100000000000000 : ℝ)^3529 := by
    have hnat : (543036089 : ℕ)^4553*100000000000000^3529 ≤ 45486726213171^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543036089 1000000000 45486726213171 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323657711/2500000000 : ℝ), (-27212353/156250000 : ℝ), (543036089/1000000000 : ℝ)] ![(44025253282853/100000000000000 : ℝ), (1311002560743/12500000000000 : ℝ), (45486726213171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323657711/2500000000 : ℝ)|^4553 ≤ (44025253282853/100000000000000 : ℝ)^3529
        have hw : |(1323657711/2500000000 : ℝ)|=(1323657711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27212353/156250000 : ℝ)|^4553 ≤ (1311002560743/12500000000000 : ℝ)^3529
        have hw : |(-27212353/156250000 : ℝ)|=(27212353/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543036089/1000000000 : ℝ)|^4553 ≤ (45486726213171/100000000000000 : ℝ)^3529
        have hw : |(543036089/1000000000 : ℝ)|=(543036089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s4_6 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647315423/5000000000 : ℝ)*x 0 + (1357590223/2500000000 : ℝ)*x 1 + (-1741590587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647315423/5000000000 : ℝ)^4553 ≤ (44025253304309/100000000000000 : ℝ)^3529 := by
    have hnat : (2647315423 : ℕ)^4553*100000000000000^3529 ≤ 44025253304309^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647315423 5000000000 44025253304309 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357590223/2500000000 : ℝ)^4553 ≤ (9097345246957/20000000000000 : ℝ)^3529 := by
    have hnat : (1357590223 : ℕ)^4553*20000000000000^3529 ≤ 9097345246957^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357590223 2500000000 9097345246957 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1741590587/10000000000 : ℝ)^4553 ≤ (1311002555887/12500000000000 : ℝ)^3529 := by
    have hnat : (1741590587 : ℕ)^4553*12500000000000^3529 ≤ 1311002555887^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741590587 10000000000 1311002555887 12500000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647315423/5000000000 : ℝ), (1357590223/2500000000 : ℝ), (-1741590587/10000000000 : ℝ)] ![(44025253304309/100000000000000 : ℝ), (9097345246957/20000000000000 : ℝ), (1311002555887/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647315423/5000000000 : ℝ)|^4553 ≤ (44025253304309/100000000000000 : ℝ)^3529
        have hw : |(2647315423/5000000000 : ℝ)|=(2647315423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357590223/2500000000 : ℝ)|^4553 ≤ (9097345246957/20000000000000 : ℝ)^3529
        have hw : |(1357590223/2500000000 : ℝ)|=(1357590223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1741590587/10000000000 : ℝ)|^4553 ≤ (1311002555887/12500000000000 : ℝ)^3529
        have hw : |(-1741590587/10000000000 : ℝ)|=(1741590587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s4_7 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66600231/156250000 : ℝ)*x 0 + (4510323453/10000000000 : ℝ)*x 1 + (805231469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66600231/156250000 : ℝ)^4553 ≤ (33280814677409/100000000000000 : ℝ)^3529 := by
    have hnat : (66600231 : ℕ)^4553*100000000000000^3529 ≤ 33280814677409^3529*156250000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66600231 156250000 33280814677409 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510323453/10000000000 : ℝ)^4553 ≤ (8949733728859/25000000000000 : ℝ)^3529 := by
    have hnat : (4510323453 : ℕ)^4553*25000000000000^3529 ≤ 8949733728859^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510323453 10000000000 8949733728859 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805231469/2000000000 : ℝ)^4553 ≤ (15460125196793/50000000000000 : ℝ)^3529 := by
    have hnat : (805231469 : ℕ)^4553*50000000000000^3529 ≤ 15460125196793^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805231469 2000000000 15460125196793 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66600231/156250000 : ℝ), (4510323453/10000000000 : ℝ), (805231469/2000000000 : ℝ)] ![(33280814677409/100000000000000 : ℝ), (8949733728859/25000000000000 : ℝ), (15460125196793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66600231/156250000 : ℝ)|^4553 ≤ (33280814677409/100000000000000 : ℝ)^3529
        have hw : |(66600231/156250000 : ℝ)|=(66600231/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510323453/10000000000 : ℝ)|^4553 ≤ (8949733728859/25000000000000 : ℝ)^3529
        have hw : |(4510323453/10000000000 : ℝ)|=(4510323453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805231469/2000000000 : ℝ)|^4553 ≤ (15460125196793/50000000000000 : ℝ)^3529
        have hw : |(805231469/2000000000 : ℝ)|=(805231469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1528_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1097/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15541/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2731/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15541/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2731/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15541/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2731/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15541/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2731/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15541/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2731/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15541/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2731/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2731/25000 : ℝ) ^ (4551/1024 : ℝ) ≤ (5324087608533181/100000000000000000000 : ℝ) := by
    have hpowers : (2731/25000 : ℝ)^4551 ≤ (5324087608533181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2731 : ℕ)^4551*100000000000000000000^1024 ≤ 5324087608533181^1024*25000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2731 25000 5324087608533181 100000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2731/25000 : ℝ)) (X := (5324087608533181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15541/100000 : ℝ) ^ (4551/1024 : ℝ) ≤ (25507088421699117/100000000000000000000 : ℝ) := by
    have hpowers : (15541/100000 : ℝ)^4551 ≤ (25507088421699117/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15541 : ℕ)^4551*100000000000000000000^1024 ≤ 25507088421699117^1024*100000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15541 100000 25507088421699117 100000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15541/100000 : ℝ)) (X := (25507088421699117/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005324087608533181/50000000000000000000 : ℝ) ≤ (3906343585901/3906250000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (50005324087608533181/50000000000000000000 : ℝ)^1024 ≤ (3906343585901/3906250000000 : ℝ)^4551 := by
      have hnat : (50005324087608533181 : ℕ)^1024*3906250000000^4551 ≤ 3906343585901^4551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005324087608533181 50000000000000000000 3906343585901 3906250000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3906343585901/3906250000000 : ℝ)) (X := (50005324087608533181/50000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015415588015116149/50000000000000000000 : ℝ) ≤ (10000693635533771/10000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (50015415588015116149/50000000000000000000 : ℝ)^1024 ≤ (10000693635533771/10000000000000000 : ℝ)^4551 := by
      have hnat : (50015415588015116149 : ℕ)^1024*10000000000000000^4551 ≤ 10000693635533771^4551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015415588015116149 50000000000000000000 10000693635533771 10000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000693635533771/10000000000000000 : ℝ)) (X := (50015415588015116149/50000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025507088421699117/50000000000000000000 : ℝ) ≤ (5000573845580491/5000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (50025507088421699117/50000000000000000000 : ℝ)^1024 ≤ (5000573845580491/5000000000000000 : ℝ)^4551 := by
      have hnat : (50025507088421699117 : ℕ)^1024*5000000000000000^4551 ≤ 5000573845580491^4551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025507088421699117 50000000000000000000 5000573845580491 5000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000573845580491/5000000000000000 : ℝ)) (X := (50025507088421699117/50000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5324087608533181/100000000000000000000 : ℝ) ≤ ((1923382747211886733/1923750000000000000 : ℝ)+2*(151351875737/153900000000000 : ℝ)*(2731/25000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (1923382747211886733/1923750000000000000 : ℝ)+2*(151351875737/153900000000000 : ℝ)*(2731/25000 : ℝ)=(3906343585901/3906250000000 : ℝ) by norm_num, show 1+2*(5324087608533181/100000000000000000000 : ℝ)=(50005324087608533181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25507088421699117/100000000000000000000 : ℝ)+(5324087608533181/100000000000000000000 : ℝ) ≤ ((1923382747211886733/1923750000000000000 : ℝ)+(151351875737/153900000000000 : ℝ)*((15541/100000 : ℝ)+(2731/25000 : ℝ)))^(4551/1024 : ℝ) := by
    rw [show (1923382747211886733/1923750000000000000 : ℝ)+(151351875737/153900000000000 : ℝ)*((15541/100000 : ℝ)+(2731/25000 : ℝ))=(10000693635533771/10000000000000000 : ℝ) by norm_num, show 1+(25507088421699117/100000000000000000000 : ℝ)+(5324087608533181/100000000000000000000 : ℝ)=(50015415588015116149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25507088421699117/100000000000000000000 : ℝ) ≤ ((1923382747211886733/1923750000000000000 : ℝ)+2*(151351875737/153900000000000 : ℝ)*(15541/100000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (1923382747211886733/1923750000000000000 : ℝ)+2*(151351875737/153900000000000 : ℝ)*(15541/100000 : ℝ)=(5000573845580491/5000000000000000 : ℝ) by norm_num, show 1+2*(25507088421699117/100000000000000000000 : ℝ)=(50025507088421699117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1923382747211886733/1923750000000000000 : ℝ)*(X 1 0+X 2 0)+(151351875737/153900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (15541/100000 : ℝ)) (c := (1923382747211886733/1923750000000000000 : ℝ)) (alpha := (151351875737/153900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1923382747211886733/1923750000000000000 : ℝ)*(X 0 1+X 2 1)+(151351875737/153900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (15541/100000 : ℝ)) (c := (1923382747211886733/1923750000000000000 : ℝ)) (alpha := (151351875737/153900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1923382747211886733/1923750000000000000 : ℝ)*(X 0 2+X 1 2)+(151351875737/153900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (15541/100000 : ℝ)) (c := (1923382747211886733/1923750000000000000 : ℝ)) (alpha := (151351875737/153900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1844588577/10000000000 : ℝ)*X 0 0+(678934213/1250000000 : ℝ)*X 0 1+(1304530621/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675384683/5000000000 : ℝ)*X 1 0+(-976914559/5000000000 : ℝ)*X 1 1+(5218122699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668846211/1250000000 : ℝ)*X 2 0+(1043624479/2000000000 : ℝ)*X 2 1+(-1953829091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34098797/80000000 : ℝ)*X 0 0+(4023605021/10000000000 : ℝ)*X 0 1+(564107089/1250000000 : ℝ)*X 0 2+(34098797/80000000 : ℝ)*X 1 0+(4023605021/10000000000 : ℝ)*X 1 1+(564107089/1250000000 : ℝ)*X 1 2+(34098797/80000000 : ℝ)*X 2 0+(4023605021/10000000000 : ℝ)*X 2 1+(564107089/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-36892339/200000000 : ℝ)*X 0 0+(5219227287/10000000000 : ℝ)*X 0 1+(5430360867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323657711/2500000000 : ℝ)*X 1 0+(-27212353/156250000 : ℝ)*X 1 1+(543036089/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647315423/5000000000 : ℝ)*X 2 0+(1357590223/2500000000 : ℝ)*X 2 1+(-1741590587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((66600231/156250000 : ℝ)*X 0 0+(4510323453/10000000000 : ℝ)*X 0 1+(805231469/2000000000 : ℝ)*X 0 2+(66600231/156250000 : ℝ)*X 1 0+(4510323453/10000000000 : ℝ)*X 1 1+(805231469/2000000000 : ℝ)*X 1 2+(66600231/156250000 : ℝ)*X 2 0+(4510323453/10000000000 : ℝ)*X 2 1+(805231469/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6276139575519770018436803/667968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (60251509/4000000000000 : ℝ)*(base19) + (337806257/20000000000000 : ℝ)*(base23) + (53144503/100000000000000 : ℝ)*(lower2) + (271999587/100000000000000 : ℝ)*(upper3) + (4232641/1562500000000 : ℝ)*(upper5) + (841389516525129/25000000000000 : ℝ)*(major0) + (841389516525129/25000000000000 : ℝ)*(major1) + (841389516525129/25000000000000 : ℝ)*(major2) + (937426017167747/20000000000000 : ℝ)*(sp0) + (4687154449639467/100000000000000 : ℝ)*(sp1) + (4687154266895907/100000000000000 : ℝ)*(sp2) + (1021974120028639/50000000000000 : ℝ)*(sp3) + (3233761057/12500000000000 : ℝ)*(sp4) + (5811510641/50000000000000 : ℝ)*(sp7) + (12774749144241/625000000000 : ℝ)*(f.failure) + (585894494490899/12500000000000 : ℝ)*(f.sum) + (8987100523969/2565000000000000000000000000 : ℝ)*base65 + (265836440085042019/16031250000000000000000000000000 : ℝ)*base67 + (64342986569854519/16031250000000000000000000000000 : ℝ)*base69 + (101583797671542019/16031250000000000000000000000000 : ℝ)*base71 + (952151032847/1282500000000000000000000000 : ℝ)*base73 + (11428593771801731/16031250000000000000000000000000 : ℝ)*base76 + (81405277820854519/16031250000000000000000000000000 : ℝ)*base77 + (91825013276010769/16031250000000000000000000000000 : ℝ)*base79 + (7720645515521/2565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (161361/15625000000000000000 : ℝ)*base90 + (161361/15625000000000000000 : ℝ)*base92 + (161361/15625000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25474834218801562056268219/5343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (728807049/100000000000000 : ℝ)*(base19) + (207368517/25000000000000 : ℝ)*(base23) + (12106337/12500000000000 : ℝ)*(upper3) + (44207099/100000000000000 : ℝ)*(lower4) + (97366031/100000000000000 : ℝ)*(upper5) + (1700436012523557/50000000000000 : ℝ)*(major0) + (1700436012523557/50000000000000 : ℝ)*(major1) + (1700436012523557/50000000000000 : ℝ)*(major2) + (465668121/4000000000000 : ℝ)*(sp1) + (3273130587/25000000000000 : ℝ)*(sp2) + (4736337268529187/100000000000000 : ℝ)*(sp4) + (4736324898019113/100000000000000 : ℝ)*(sp5) + (4736323346532771/100000000000000 : ℝ)*(sp6) + (258175827832211/12500000000000 : ℝ)*(sp7) + (258175827832211/12500000000000 : ℝ)*(f.failure) + (4736337268529187/100000000000000 : ℝ)*(f.sum) + (1762870618403/320625000000000000000000000 : ℝ)*base66 + (86022183709731427/32062500000000000000000000000000 : ℝ)*base67 + (278568360395481427/32062500000000000000000000000000 : ℝ)*base69 + (109638440706418927/32062500000000000000000000000000 : ℝ)*base71 + (1223388276959/641250000000000000000000000 : ℝ)*base73 + (222618338713731427/32062500000000000000000000000000 : ℝ)*base75 + (71272832569918927/32062500000000000000000000000000 : ℝ)*base77 + (553325120878543927/32062500000000000000000000000000 : ℝ)*base79 + (1239001906031/2565000000000000000000000000 : ℝ)*base81 + (425269/312500000000000000000 : ℝ)*base89 + (425269/312500000000000000000 : ℝ)*base91 + (425269/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1528_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1528_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1528_s5_0 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-922316331/5000000000 : ℝ)*x 0 + (1357797767/2500000000 : ℝ)*x 1 + (260918791/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (922316331/5000000000 : ℝ)^4553 ≤ (451815395319/4000000000000 : ℝ)^3529 := by
    have hnat : (922316331 : ℕ)^4553*4000000000000^3529 ≤ 451815395319^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922316331 5000000000 451815395319 4000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357797767/2500000000 : ℝ)^4553 ≤ (22747849040141/50000000000000 : ℝ)^3529 := by
    have hnat : (1357797767 : ℕ)^4553*50000000000000^3529 ≤ 22747849040141^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357797767 2500000000 22747849040141 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260918791/500000000 : ℝ)^4553 ≤ (43208917022057/100000000000000 : ℝ)^3529 := by
    have hnat : (260918791 : ℕ)^4553*100000000000000^3529 ≤ 43208917022057^3529*500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260918791 500000000 43208917022057 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-922316331/5000000000 : ℝ), (1357797767/2500000000 : ℝ), (260918791/500000000 : ℝ)] ![(451815395319/4000000000000 : ℝ), (22747849040141/50000000000000 : ℝ), (43208917022057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-922316331/5000000000 : ℝ)|^4553 ≤ (451815395319/4000000000000 : ℝ)^3529
        have hw : |(-922316331/5000000000 : ℝ)|=(922316331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357797767/2500000000 : ℝ)|^4553 ≤ (22747849040141/50000000000000 : ℝ)^3529
        have hw : |(1357797767/2500000000 : ℝ)|=(1357797767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260918791/500000000 : ℝ)|^4553 ≤ (43208917022057/100000000000000 : ℝ)^3529
        have hw : |(260918791/500000000 : ℝ)|=(260918791/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s5_1 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350693839/10000000000 : ℝ)*x 0 + (-195359239/1000000000 : ℝ)*x 1 + (1304594197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350693839/10000000000 : ℝ)^4553 ≤ (22313804801629/50000000000000 : ℝ)^3529 := by
    have hnat : (5350693839 : ℕ)^4553*50000000000000^3529 ≤ 22313804801629^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350693839 10000000000 22313804801629 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195359239/1000000000 : ℝ)^4553 ≤ (12163463017209/100000000000000 : ℝ)^3529 := by
    have hnat : (195359239 : ℕ)^4553*100000000000000^3529 ≤ 12163463017209^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195359239 1000000000 12163463017209 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304594197/2500000000 : ℝ)^4553 ≤ (21604463681491/50000000000000 : ℝ)^3529 := by
    have hnat : (1304594197 : ℕ)^4553*50000000000000^3529 ≤ 21604463681491^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304594197 2500000000 21604463681491 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350693839/10000000000 : ℝ), (-195359239/1000000000 : ℝ), (1304594197/2500000000 : ℝ)] ![(22313804801629/50000000000000 : ℝ), (12163463017209/100000000000000 : ℝ), (21604463681491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350693839/10000000000 : ℝ)|^4553 ≤ (22313804801629/50000000000000 : ℝ)^3529
        have hw : |(5350693839/10000000000 : ℝ)|=(5350693839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195359239/1000000000 : ℝ)|^4553 ≤ (12163463017209/100000000000000 : ℝ)^3529
        have hw : |(-195359239/1000000000 : ℝ)|=(195359239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304594197/2500000000 : ℝ)|^4553 ≤ (21604463681491/50000000000000 : ℝ)^3529
        have hw : |(1304594197/2500000000 : ℝ)|=(1304594197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s5_2 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675347381/5000000000 : ℝ)*x 0 + (81537109/156250000 : ℝ)*x 1 + (-976796781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675347381/5000000000 : ℝ)^4553 ≤ (22313809767681/50000000000000 : ℝ)^3529 := by
    have hnat : (2675347381 : ℕ)^4553*50000000000000^3529 ≤ 22313809767681^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675347381 5000000000 22313809767681 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81537109/156250000 : ℝ)^4553 ≤ (10802227001449/25000000000000 : ℝ)^3529 := by
    have hnat : (81537109 : ℕ)^4553*25000000000000^3529 ≤ 10802227001449^3529*156250000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81537109 156250000 10802227001449 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976796781/5000000000 : ℝ)^4553 ≤ (6081736215851/50000000000000 : ℝ)^3529 := by
    have hnat : (976796781 : ℕ)^4553*50000000000000^3529 ≤ 6081736215851^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976796781 5000000000 6081736215851 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675347381/5000000000 : ℝ), (81537109/156250000 : ℝ), (-976796781/5000000000 : ℝ)] ![(22313809767681/50000000000000 : ℝ), (10802227001449/25000000000000 : ℝ), (6081736215851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675347381/5000000000 : ℝ)|^4553 ≤ (22313809767681/50000000000000 : ℝ)^3529
        have hw : |(2675347381/5000000000 : ℝ)|=(2675347381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81537109/156250000 : ℝ)|^4553 ≤ (10802227001449/25000000000000 : ℝ)^3529
        have hw : |(81537109/156250000 : ℝ)|=(81537109/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-976796781/5000000000 : ℝ)|^4553 ≤ (6081736215851/50000000000000 : ℝ)^3529
        have hw : |(-976796781/5000000000 : ℝ)|=(976796781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s5_3 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2131187149/5000000000 : ℝ)*x 0 + (804843571/2000000000 : ℝ)*x 1 + (902447931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131187149/5000000000 : ℝ)^4553 ≤ (8320101709661/25000000000000 : ℝ)^3529 := by
    have hnat : (2131187149 : ℕ)^4553*25000000000000^3529 ≤ 8320101709661^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131187149 5000000000 8320101709661 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804843571/2000000000 : ℝ)^4553 ≤ (30901034727731/100000000000000 : ℝ)^3529 := by
    have hnat : (804843571 : ℕ)^4553*100000000000000^3529 ≤ 30901034727731^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804843571 2000000000 30901034727731 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902447931/2000000000 : ℝ)^4553 ≤ (4477319801901/12500000000000 : ℝ)^3529 := by
    have hnat : (902447931 : ℕ)^4553*12500000000000^3529 ≤ 4477319801901^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902447931 2000000000 4477319801901 12500000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2131187149/5000000000 : ℝ), (804843571/2000000000 : ℝ), (902447931/2000000000 : ℝ)] ![(8320101709661/25000000000000 : ℝ), (30901034727731/100000000000000 : ℝ), (4477319801901/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2131187149/5000000000 : ℝ)|^4553 ≤ (8320101709661/25000000000000 : ℝ)^3529
        have hw : |(2131187149/5000000000 : ℝ)|=(2131187149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804843571/2000000000 : ℝ)|^4553 ≤ (30901034727731/100000000000000 : ℝ)^3529
        have hw : |(804843571/2000000000 : ℝ)|=(804843571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902447931/2000000000 : ℝ)|^4553 ≤ (4477319801901/12500000000000 : ℝ)^3529
        have hw : |(902447931/2000000000 : ℝ)|=(902447931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s5_4 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844661391/10000000000 : ℝ)*x 0 + (5219474911/10000000000 : ℝ)*x 1 + (1086016717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844661391/10000000000 : ℝ)^4553 ≤ (2259122369567/20000000000000 : ℝ)^3529 := by
    have hnat : (1844661391 : ℕ)^4553*20000000000000^3529 ≤ 2259122369567^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844661391 10000000000 2259122369567 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219474911/10000000000 : ℝ)^4553 ≤ (21610329360513/50000000000000 : ℝ)^3529 := by
    have hnat : (5219474911 : ℕ)^4553*50000000000000^3529 ≤ 21610329360513^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219474911 10000000000 21610329360513 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086016717/2000000000 : ℝ)^4553 ≤ (11370932355531/25000000000000 : ℝ)^3529 := by
    have hnat : (1086016717 : ℕ)^4553*25000000000000^3529 ≤ 11370932355531^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086016717 2000000000 11370932355531 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844661391/10000000000 : ℝ), (5219474911/10000000000 : ℝ), (1086016717/2000000000 : ℝ)] ![(2259122369567/20000000000000 : ℝ), (21610329360513/50000000000000 : ℝ), (11370932355531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844661391/10000000000 : ℝ)|^4553 ≤ (2259122369567/20000000000000 : ℝ)^3529
        have hw : |(-1844661391/10000000000 : ℝ)|=(1844661391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219474911/10000000000 : ℝ)|^4553 ≤ (21610329360513/50000000000000 : ℝ)^3529
        have hw : |(5219474911/10000000000 : ℝ)|=(5219474911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086016717/2000000000 : ℝ)|^4553 ≤ (11370932355531/25000000000000 : ℝ)^3529
        have hw : |(1086016717/2000000000 : ℝ)|=(1086016717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s5_5 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330918581/625000000 : ℝ)*x 0 + (-1741884799/10000000000 : ℝ)*x 1 + (5430083401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330918581/625000000 : ℝ)^4553 ≤ (44025966170381/100000000000000 : ℝ)^3529 := by
    have hnat : (330918581 : ℕ)^4553*100000000000000^3529 ≤ 44025966170381^3529*625000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330918581 625000000 44025966170381 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1741884799/10000000000 : ℝ)^4553 ≤ (10490306385241/100000000000000 : ℝ)^3529 := by
    have hnat : (1741884799 : ℕ)^4553*100000000000000^3529 ≤ 10490306385241^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741884799 10000000000 10490306385241 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430083401/10000000000 : ℝ)^4553 ≤ (568546592921/1250000000000 : ℝ)^3529 := by
    have hnat : (5430083401 : ℕ)^4553*1250000000000^3529 ≤ 568546592921^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430083401 10000000000 568546592921 1250000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330918581/625000000 : ℝ), (-1741884799/10000000000 : ℝ), (5430083401/10000000000 : ℝ)] ![(44025966170381/100000000000000 : ℝ), (10490306385241/100000000000000 : ℝ), (568546592921/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330918581/625000000 : ℝ)|^4553 ≤ (44025966170381/100000000000000 : ℝ)^3529
        have hw : |(330918581/625000000 : ℝ)|=(330918581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1741884799/10000000000 : ℝ)|^4553 ≤ (10490306385241/100000000000000 : ℝ)^3529
        have hw : |(-1741884799/10000000000 : ℝ)|=(1741884799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430083401/10000000000 : ℝ)|^4553 ≤ (568546592921/1250000000000 : ℝ)^3529
        have hw : |(5430083401/10000000000 : ℝ)|=(5430083401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s5_6 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529469719/1000000000 : ℝ)*x 0 + (1086016683/2000000000 : ℝ)*x 1 + (-870942463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529469719/1000000000 : ℝ)^4553 ≤ (44025965033227/100000000000000 : ℝ)^3529 := by
    have hnat : (529469719 : ℕ)^4553*100000000000000^3529 ≤ 44025965033227^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529469719 1000000000 44025965033227 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086016683/2000000000 : ℝ)^4553 ≤ (1819349103399/4000000000000 : ℝ)^3529 := by
    have hnat : (1086016683 : ℕ)^4553*4000000000000^3529 ≤ 1819349103399^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086016683 2000000000 1819349103399 4000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870942463/5000000000 : ℝ)^4553 ≤ (655644210751/6250000000000 : ℝ)^3529 := by
    have hnat : (870942463 : ℕ)^4553*6250000000000^3529 ≤ 655644210751^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870942463 5000000000 655644210751 6250000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529469719/1000000000 : ℝ), (1086016683/2000000000 : ℝ), (-870942463/5000000000 : ℝ)] ![(44025965033227/100000000000000 : ℝ), (1819349103399/4000000000000 : ℝ), (655644210751/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529469719/1000000000 : ℝ)|^4553 ≤ (44025965033227/100000000000000 : ℝ)^3529
        have hw : |(529469719/1000000000 : ℝ)|=(529469719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086016683/2000000000 : ℝ)|^4553 ≤ (1819349103399/4000000000000 : ℝ)^3529
        have hw : |(1086016683/2000000000 : ℝ)|=(1086016683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-870942463/5000000000 : ℝ)|^4553 ≤ (655644210751/6250000000000 : ℝ)^3529
        have hw : |(-870942463/5000000000 : ℝ)|=(870942463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s5_7 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852488159/2000000000 : ℝ)*x 0 + (901943693/2000000000 : ℝ)*x 1 + (4026756129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852488159/2000000000 : ℝ)^4553 ≤ (33281076701767/100000000000000 : ℝ)^3529 := by
    have hnat : (852488159 : ℕ)^4553*100000000000000^3529 ≤ 33281076701767^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852488159 2000000000 33281076701767 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901943693/2000000000 : ℝ)^4553 ≤ (357927398383/1000000000000 : ℝ)^3529 := by
    have hnat : (901943693 : ℕ)^4553*1000000000000^3529 ≤ 357927398383^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901943693 2000000000 357927398383 1000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4026756129/10000000000 : ℝ)^4553 ≤ (15463091720427/50000000000000 : ℝ)^3529 := by
    have hnat : (4026756129 : ℕ)^4553*50000000000000^3529 ≤ 15463091720427^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026756129 10000000000 15463091720427 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852488159/2000000000 : ℝ), (901943693/2000000000 : ℝ), (4026756129/10000000000 : ℝ)] ![(33281076701767/100000000000000 : ℝ), (357927398383/1000000000000 : ℝ), (15463091720427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852488159/2000000000 : ℝ)|^4553 ≤ (33281076701767/100000000000000 : ℝ)^3529
        have hw : |(852488159/2000000000 : ℝ)|=(852488159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901943693/2000000000 : ℝ)|^4553 ≤ (357927398383/1000000000000 : ℝ)^3529
        have hw : |(901943693/2000000000 : ℝ)|=(901943693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4026756129/10000000000 : ℝ)|^4553 ≤ (15463091720427/50000000000000 : ℝ)^3529
        have hw : |(4026756129/10000000000 : ℝ)|=(4026756129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1528_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (343/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (1097/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1097/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1097/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1097/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1097/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1097/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (1097/10000 : ℝ) ^ (4551/1024 : ℝ) ≤ (1356112849486159/25000000000000000000 : ℝ) := by
    have hpowers : (1097/10000 : ℝ)^4551 ≤ (1356112849486159/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1097 : ℕ)^4551*25000000000000000000^1024 ≤ 1356112849486159^1024*10000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1097 10000 1356112849486159 25000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1097/10000 : ℝ)) (X := (1356112849486159/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4551/1024 : ℝ) ≤ (25137171515457661/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4551 ≤ (25137171515457661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4551*100000000000000000000^1024 ≤ 25137171515457661^1024*10000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 25137171515457661 100000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (25137171515457661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501356112849486159/12500000000000000000 : ℝ) ≤ (250006102400279/250000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (12501356112849486159/12500000000000000000 : ℝ)^1024 ≤ (250006102400279/250000000000000 : ℝ)^4551 := by
      have hnat : (12501356112849486159 : ℕ)^1024*250000000000000^4551 ≤ 250006102400279^4551*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501356112849486159 12500000000000000000 250006102400279 250000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250006102400279/250000000000000 : ℝ)) (X := (12501356112849486159/12500000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030561622913402297/100000000000000000000 : ℝ) ≤ (5000343785941517/5000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (100030561622913402297/100000000000000000000 : ℝ)^1024 ≤ (5000343785941517/5000000000000000 : ℝ)^4551 := by
      have hnat : (100030561622913402297 : ℕ)^1024*5000000000000000^4551 ≤ 5000343785941517^4551*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030561622913402297 100000000000000000000 5000343785941517 5000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000343785941517/5000000000000000 : ℝ)) (X := (100030561622913402297/100000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025137171515457661/50000000000000000000 : ℝ) ≤ (2500282761938727/2500000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (50025137171515457661/50000000000000000000 : ℝ)^1024 ≤ (2500282761938727/2500000000000000 : ℝ)^4551 := by
      have hnat : (50025137171515457661 : ℕ)^1024*2500000000000000^4551 ≤ 2500282761938727^4551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025137171515457661 50000000000000000000 2500282761938727 2500000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500282761938727/2500000000000000 : ℝ)) (X := (50025137171515457661/50000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1356112849486159/25000000000000000000 : ℝ) ≤ ((1129784336333538191/1130000000000000000 : ℝ)+2*(221737935937/226000000000000 : ℝ)*(1097/10000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (1129784336333538191/1130000000000000000 : ℝ)+2*(221737935937/226000000000000 : ℝ)*(1097/10000 : ℝ)=(250006102400279/250000000000000 : ℝ) by norm_num, show 1+2*(1356112849486159/25000000000000000000 : ℝ)=(12501356112849486159/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25137171515457661/100000000000000000000 : ℝ)+(1356112849486159/25000000000000000000 : ℝ) ≤ ((1129784336333538191/1130000000000000000 : ℝ)+(221737935937/226000000000000 : ℝ)*((1549/10000 : ℝ)+(1097/10000 : ℝ)))^(4551/1024 : ℝ) := by
    rw [show (1129784336333538191/1130000000000000000 : ℝ)+(221737935937/226000000000000 : ℝ)*((1549/10000 : ℝ)+(1097/10000 : ℝ))=(5000343785941517/5000000000000000 : ℝ) by norm_num, show 1+(25137171515457661/100000000000000000000 : ℝ)+(1356112849486159/25000000000000000000 : ℝ)=(100030561622913402297/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25137171515457661/100000000000000000000 : ℝ) ≤ ((1129784336333538191/1130000000000000000 : ℝ)+2*(221737935937/226000000000000 : ℝ)*(1549/10000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (1129784336333538191/1130000000000000000 : ℝ)+2*(221737935937/226000000000000 : ℝ)*(1549/10000 : ℝ)=(2500282761938727/2500000000000000 : ℝ) by norm_num, show 1+2*(25137171515457661/100000000000000000000 : ℝ)=(50025137171515457661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1129784336333538191/1130000000000000000 : ℝ)*(X 1 0+X 2 0)+(221737935937/226000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1129784336333538191/1130000000000000000 : ℝ)) (alpha := (221737935937/226000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1129784336333538191/1130000000000000000 : ℝ)*(X 0 1+X 2 1)+(221737935937/226000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1129784336333538191/1130000000000000000 : ℝ)) (alpha := (221737935937/226000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1129784336333538191/1130000000000000000 : ℝ)*(X 0 2+X 1 2)+(221737935937/226000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1129784336333538191/1130000000000000000 : ℝ)) (alpha := (221737935937/226000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-922316331/5000000000 : ℝ)*X 0 0+(1357797767/2500000000 : ℝ)*X 0 1+(260918791/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350693839/10000000000 : ℝ)*X 1 0+(-195359239/1000000000 : ℝ)*X 1 1+(1304594197/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675347381/5000000000 : ℝ)*X 2 0+(81537109/156250000 : ℝ)*X 2 1+(-976796781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2131187149/5000000000 : ℝ)*X 0 0+(804843571/2000000000 : ℝ)*X 0 1+(902447931/2000000000 : ℝ)*X 0 2+(2131187149/5000000000 : ℝ)*X 1 0+(804843571/2000000000 : ℝ)*X 1 1+(902447931/2000000000 : ℝ)*X 1 2+(2131187149/5000000000 : ℝ)*X 2 0+(804843571/2000000000 : ℝ)*X 2 1+(902447931/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1844661391/10000000000 : ℝ)*X 0 0+(5219474911/10000000000 : ℝ)*X 0 1+(1086016717/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330918581/625000000 : ℝ)*X 1 0+(-1741884799/10000000000 : ℝ)*X 1 1+(5430083401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529469719/1000000000 : ℝ)*X 2 0+(1086016683/2000000000 : ℝ)*X 2 1+(-870942463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((852488159/2000000000 : ℝ)*X 0 0+(901943693/2000000000 : ℝ)*X 0 1+(4026756129/10000000000 : ℝ)*X 0 2+(852488159/2000000000 : ℝ)*X 1 0+(901943693/2000000000 : ℝ)*X 1 1+(4026756129/10000000000 : ℝ)*X 1 2+(852488159/2000000000 : ℝ)*X 2 0+(901943693/2000000000 : ℝ)*X 2 1+(4026756129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120642070346014870885321311/28250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (762620387/100000000000000 : ℝ)*(base15) + (73641561/100000000000000 : ℝ)*(upper2) + (32454133/100000000000000 : ℝ)*(upper4) + (70111533/25000000000000 : ℝ)*(lower5) + (3374012171121607/100000000000000 : ℝ)*(major0) + (3374012171121607/100000000000000 : ℝ)*(major1) + (3374012171121607/100000000000000 : ℝ)*(major2) + (4698927329729651/100000000000000 : ℝ)*(sp0) + (4698929254416161/100000000000000 : ℝ)*(sp1) + (4698908528050889/100000000000000 : ℝ)*(sp2) + (409818221039693/20000000000000 : ℝ)*(sp3) + (167956681/6250000000000 : ℝ)*(sp4) + (10744492829/50000000000000 : ℝ)*(sp6) + (384707209/12500000000000 : ℝ)*(sp7) + (2049094182856137/100000000000000 : ℝ)*(f.failure) + (4698930017036547/100000000000000 : ℝ)*(f.sum) + (80017188305159/11300000000000000000000000000 : ℝ)*base65 + (328385945266587937/113000000000000000000000000000000 : ℝ)*base67 + (450431825765412063/113000000000000000000000000000000 : ℝ)*base70 + (580378621763412063/113000000000000000000000000000000 : ℝ)*base72 + (61740311196259/11300000000000000000000000000 : ℝ)*base73 + (372702503109412063/113000000000000000000000000000000 : ℝ)*base76 + (15368718330412063/113000000000000000000000000000000 : ℝ)*base78 + (428213714463412063/113000000000000000000000000000000 : ℝ)*base80 + (3037414217341/11300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7785023/2500000000000000000000 : ℝ)*base89 + (7785023/2500000000000000000000 : ℝ)*base91 + (7785023/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182817117191920935106403037/56500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16546781/2000000000000 : ℝ)*(base19) + (90771631/12500000000000 : ℝ)*(base23) + (75051069/50000000000000 : ℝ)*(lower1) + (76329037/100000000000000 : ℝ)*(upper3) + (2754137/20000000000000 : ℝ)*(lower4) + (43821927/50000000000000 : ℝ)*(upper5) + (3409343037577569/100000000000000 : ℝ)*(major0) + (3409343037577569/100000000000000 : ℝ)*(major1) + (3409343037577569/100000000000000 : ℝ)*(major2) + (607351757/20000000000000 : ℝ)*(sp1) + (4748134756649139/100000000000000 : ℝ)*(sp4) + (4748130892551303/100000000000000 : ℝ)*(sp5) + (4748134030476091/100000000000000 : ℝ)*(sp6) + (1035275605324643/50000000000000 : ℝ)*(sp7) + (1035275605324643/50000000000000 : ℝ)*(f.failure) + (4748134756649139/100000000000000 : ℝ)*(f.sum) + (41583239040147/11300000000000000000000000000 : ℝ)*base66 + (370674288574797321/113000000000000000000000000000000 : ℝ)*base68 + (429065862244797321/113000000000000000000000000000000 : ℝ)*base70 + (324740585676797321/113000000000000000000000000000000 : ℝ)*base72 + (66566936998747/11300000000000000000000000000 : ℝ)*base74 + (692795790971202679/113000000000000000000000000000000 : ℝ)*base75 + (1614735250207797321/113000000000000000000000000000000 : ℝ)*base78 + (210950369057202679/113000000000000000000000000000000 : ℝ)*base79 + (104002123400753/11300000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7384597/1250000000000000000000 : ℝ)*base89 + (7384597/1250000000000000000000 : ℝ)*base91 + (7384597/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1528_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1528_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1528_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15939/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5279/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1528_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1528_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1528_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15939/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5279/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1528_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
