-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1540_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:07:28.083519+00:00
-- url     : https://prove2.me/submissions/9d5a455d-9578-469a-812d-3465f28e2a0d

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
theorem support_rectangle_w1540_s3_0 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-913537469/5000000000 : ℝ)*x 0 + (5431987827/10000000000 : ℝ)*x 1 + (5216792441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913537469/5000000000 : ℝ)^4577 ≤ (11194102155427/100000000000000 : ℝ)^3553 := by
    have hnat : (913537469 : ℕ)^4577*100000000000000^3553 ≤ 11194102155427^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913537469 5000000000 11194102155427 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431987827/10000000000 : ℝ)^4577 ≤ (45558772679631/100000000000000 : ℝ)^3553 := by
    have hnat : (5431987827 : ℕ)^4577*100000000000000^3553 ≤ 45558772679631^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431987827 10000000000 45558772679631 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216792441/10000000000 : ℝ)^4577 ≤ (43247125149859/100000000000000 : ℝ)^3553 := by
    have hnat : (5216792441 : ℕ)^4577*100000000000000^3553 ≤ 43247125149859^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216792441 10000000000 43247125149859 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-913537469/5000000000 : ℝ), (5431987827/10000000000 : ℝ), (5216792441/10000000000 : ℝ)] ![(11194102155427/100000000000000 : ℝ), (45558772679631/100000000000000 : ℝ), (43247125149859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-913537469/5000000000 : ℝ)|^4577 ≤ (11194102155427/100000000000000 : ℝ)^3553
        have hw : |(-913537469/5000000000 : ℝ)|=(913537469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431987827/10000000000 : ℝ)|^4577 ≤ (45558772679631/100000000000000 : ℝ)^3553
        have hw : |(5431987827/10000000000 : ℝ)|=(5431987827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216792441/10000000000 : ℝ)|^4577 ≤ (43247125149859/100000000000000 : ℝ)^3553
        have hw : |(5216792441/10000000000 : ℝ)|=(5216792441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s3_1 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350615683/10000000000 : ℝ)*x 0 + (-484320261/2500000000 : ℝ)*x 1 + (5216792847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350615683/10000000000 : ℝ)^4577 ≤ (44681503630579/100000000000000 : ℝ)^3553 := by
    have hnat : (5350615683 : ℕ)^4577*100000000000000^3553 ≤ 44681503630579^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350615683 10000000000 44681503630579 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484320261/2500000000 : ℝ)^4577 ≤ (6035683431943/50000000000000 : ℝ)^3553 := by
    have hnat : (484320261 : ℕ)^4577*50000000000000^3553 ≤ 6035683431943^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484320261 2500000000 6035683431943 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216792847/10000000000 : ℝ)^4577 ≤ (2162356474281/5000000000000 : ℝ)^3553 := by
    have hnat : (5216792847 : ℕ)^4577*5000000000000^3553 ≤ 2162356474281^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216792847 10000000000 2162356474281 5000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350615683/10000000000 : ℝ), (-484320261/2500000000 : ℝ), (5216792847/10000000000 : ℝ)] ![(44681503630579/100000000000000 : ℝ), (6035683431943/50000000000000 : ℝ), (2162356474281/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350615683/10000000000 : ℝ)|^4577 ≤ (44681503630579/100000000000000 : ℝ)^3553
        have hw : |(5350615683/10000000000 : ℝ)|=(5350615683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484320261/2500000000 : ℝ)|^4577 ≤ (6035683431943/50000000000000 : ℝ)^3553
        have hw : |(-484320261/2500000000 : ℝ)|=(484320261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216792847/10000000000 : ℝ)|^4577 ≤ (2162356474281/5000000000000 : ℝ)^3553
        have hw : |(5216792847/10000000000 : ℝ)|=(5216792847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s3_2 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350615879/10000000000 : ℝ)*x 0 + (208671711/400000000 : ℝ)*x 1 + (-1937280877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350615879/10000000000 : ℝ)^4577 ≤ (44681505739041/100000000000000 : ℝ)^3553 := by
    have hnat : (5350615879 : ℕ)^4577*100000000000000^3553 ≤ 44681505739041^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350615879 10000000000 44681505739041 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208671711/400000000 : ℝ)^4577 ≤ (43247128716717/100000000000000 : ℝ)^3553 := by
    have hnat : (208671711 : ℕ)^4577*100000000000000^3553 ≤ 43247128716717^3553*400000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208671711 400000000 43247128716717 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1937280877/10000000000 : ℝ)^4577 ≤ (3017841380847/25000000000000 : ℝ)^3553 := by
    have hnat : (1937280877 : ℕ)^4577*25000000000000^3553 ≤ 3017841380847^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937280877 10000000000 3017841380847 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350615879/10000000000 : ℝ), (208671711/400000000 : ℝ), (-1937280877/10000000000 : ℝ)] ![(44681505739041/100000000000000 : ℝ), (43247128716717/100000000000000 : ℝ), (3017841380847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350615879/10000000000 : ℝ)|^4577 ≤ (44681505739041/100000000000000 : ℝ)^3553
        have hw : |(5350615879/10000000000 : ℝ)|=(5350615879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208671711/400000000 : ℝ)|^4577 ≤ (43247128716717/100000000000000 : ℝ)^3553
        have hw : |(208671711/400000000 : ℝ)|=(208671711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1937280877/10000000000 : ℝ)|^4577 ≤ (3017841380847/25000000000000 : ℝ)^3553
        have hw : |(-1937280877/10000000000 : ℝ)|=(1937280877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s3_3 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128342327/5000000000 : ℝ)*x 0 + (4013906567/10000000000 : ℝ)*x 1 + (1127881439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128342327/5000000000 : ℝ)^4577 ≤ (33278766912959/100000000000000 : ℝ)^3553 := by
    have hnat : (2128342327 : ℕ)^4577*100000000000000^3553 ≤ 33278766912959^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128342327 5000000000 33278766912959 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013906567/10000000000 : ℝ)^4577 ≤ (15427036725371/50000000000000 : ℝ)^3553 := by
    have hnat : (4013906567 : ℕ)^4577*50000000000000^3553 ≤ 15427036725371^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013906567 10000000000 15427036725371 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127881439/2500000000 : ℝ)^4577 ≤ (3586715962383/10000000000000 : ℝ)^3553 := by
    have hnat : (1127881439 : ℕ)^4577*10000000000000^3553 ≤ 3586715962383^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127881439 2500000000 3586715962383 10000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128342327/5000000000 : ℝ), (4013906567/10000000000 : ℝ), (1127881439/2500000000 : ℝ)] ![(33278766912959/100000000000000 : ℝ), (15427036725371/50000000000000 : ℝ), (3586715962383/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128342327/5000000000 : ℝ)|^4577 ≤ (33278766912959/100000000000000 : ℝ)^3553
        have hw : |(2128342327/5000000000 : ℝ)|=(2128342327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013906567/10000000000 : ℝ)|^4577 ≤ (15427036725371/50000000000000 : ℝ)^3553
        have hw : |(4013906567/10000000000 : ℝ)|=(4013906567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127881439/2500000000 : ℝ)|^4577 ≤ (3586715962383/10000000000000 : ℝ)^3553
        have hw : |(1127881439/2500000000 : ℝ)|=(1127881439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s3_4 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22838797/125000000 : ℝ)*x 0 + (5217930099/10000000000 : ℝ)*x 1 + (5430842221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22838797/125000000 : ℝ)^4577 ≤ (2798582408921/25000000000000 : ℝ)^3553 := by
    have hnat : (22838797 : ℕ)^4577*25000000000000^3553 ≤ 2798582408921^3553*125000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22838797 125000000 2798582408921 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217930099/10000000000 : ℝ)^4577 ≤ (8651854965539/20000000000000 : ℝ)^3553 := by
    have hnat : (5217930099 : ℕ)^4577*20000000000000^3553 ≤ 8651854965539^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217930099 10000000000 8651854965539 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430842221/10000000000 : ℝ)^4577 ≤ (22773197759707/50000000000000 : ℝ)^3553 := by
    have hnat : (5430842221 : ℕ)^4577*50000000000000^3553 ≤ 22773197759707^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430842221 10000000000 22773197759707 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22838797/125000000 : ℝ), (5217930099/10000000000 : ℝ), (5430842221/10000000000 : ℝ)] ![(2798582408921/25000000000000 : ℝ), (8651854965539/20000000000000 : ℝ), (22773197759707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22838797/125000000 : ℝ)|^4577 ≤ (2798582408921/25000000000000 : ℝ)^3553
        have hw : |(-22838797/125000000 : ℝ)|=(22838797/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217930099/10000000000 : ℝ)|^4577 ≤ (8651854965539/20000000000000 : ℝ)^3553
        have hw : |(5217930099/10000000000 : ℝ)|=(5217930099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430842221/10000000000 : ℝ)|^4577 ≤ (22773197759707/50000000000000 : ℝ)^3553
        have hw : |(5430842221/10000000000 : ℝ)|=(5430842221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s3_5 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293897171/10000000000 : ℝ)*x 0 + (-430807799/2500000000 : ℝ)*x 1 + (5430842241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293897171/10000000000 : ℝ)^4577 ≤ (44072290911287/100000000000000 : ℝ)^3553 := by
    have hnat : (5293897171 : ℕ)^4577*100000000000000^3553 ≤ 44072290911287^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293897171 10000000000 44072290911287 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430807799/2500000000 : ℝ)^4577 ≤ (10381313336197/100000000000000 : ℝ)^3553 := by
    have hnat : (430807799 : ℕ)^4577*100000000000000^3553 ≤ 10381313336197^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430807799 2500000000 10381313336197 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430842241/10000000000 : ℝ)^4577 ≤ (711662433367/1562500000000 : ℝ)^3553 := by
    have hnat : (5430842241 : ℕ)^4577*1562500000000^3553 ≤ 711662433367^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430842241 10000000000 711662433367 1562500000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293897171/10000000000 : ℝ), (-430807799/2500000000 : ℝ), (5430842241/10000000000 : ℝ)] ![(44072290911287/100000000000000 : ℝ), (10381313336197/100000000000000 : ℝ), (711662433367/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293897171/10000000000 : ℝ)|^4577 ≤ (44072290911287/100000000000000 : ℝ)^3553
        have hw : |(5293897171/10000000000 : ℝ)|=(5293897171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430807799/2500000000 : ℝ)|^4577 ≤ (10381313336197/100000000000000 : ℝ)^3553
        have hw : |(-430807799/2500000000 : ℝ)|=(430807799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430842241/10000000000 : ℝ)|^4577 ≤ (711662433367/1562500000000 : ℝ)^3553
        have hw : |(5430842241/10000000000 : ℝ)|=(5430842241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s3_6 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646948609/5000000000 : ℝ)*x 0 + (5430842207/10000000000 : ℝ)*x 1 + (-86161559/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646948609/5000000000 : ℝ)^4577 ≤ (44072291415337/100000000000000 : ℝ)^3553 := by
    have hnat : (2646948609 : ℕ)^4577*100000000000000^3553 ≤ 44072291415337^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646948609 5000000000 44072291415337 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430842207/10000000000 : ℝ)^4577 ≤ (22773197684081/50000000000000 : ℝ)^3553 := by
    have hnat : (5430842207 : ℕ)^4577*50000000000000^3553 ≤ 22773197684081^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430842207 10000000000 22773197684081 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86161559/500000000 : ℝ)^4577 ≤ (2595328303007/25000000000000 : ℝ)^3553 := by
    have hnat : (86161559 : ℕ)^4577*25000000000000^3553 ≤ 2595328303007^3553*500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86161559 500000000 2595328303007 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646948609/5000000000 : ℝ), (5430842207/10000000000 : ℝ), (-86161559/500000000 : ℝ)] ![(44072291415337/100000000000000 : ℝ), (22773197684081/50000000000000 : ℝ), (2595328303007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646948609/5000000000 : ℝ)|^4577 ≤ (44072291415337/100000000000000 : ℝ)^3553
        have hw : |(2646948609/5000000000 : ℝ)|=(2646948609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430842207/10000000000 : ℝ)|^4577 ≤ (22773197684081/50000000000000 : ℝ)^3553
        have hw : |(5430842207/10000000000 : ℝ)|=(5430842207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86161559/500000000 : ℝ)|^4577 ≤ (2595328303007/25000000000000 : ℝ)^3553
        have hw : |(-86161559/500000000 : ℝ)|=(86161559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s3_7 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266047029/625000000 : ℝ)*x 0 + (450889513/1000000000 : ℝ)*x 1 + (200827893/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266047029/625000000 : ℝ)^4577 ≤ (8319862460741/25000000000000 : ℝ)^3553 := by
    have hnat : (266047029 : ℕ)^4577*25000000000000^3553 ≤ 8319862460741^3553*625000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266047029 625000000 8319862460741 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450889513/1000000000 : ℝ)^4577 ≤ (358402205997/1000000000000 : ℝ)^3553 := by
    have hnat : (450889513 : ℕ)^4577*1000000000000^3553 ≤ 358402205997^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450889513 1000000000 358402205997 1000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200827893/500000000 : ℝ)^4577 ≤ (15440164769081/50000000000000 : ℝ)^3553 := by
    have hnat : (200827893 : ℕ)^4577*50000000000000^3553 ≤ 15440164769081^3553*500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200827893 500000000 15440164769081 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266047029/625000000 : ℝ), (450889513/1000000000 : ℝ), (200827893/500000000 : ℝ)] ![(8319862460741/25000000000000 : ℝ), (358402205997/1000000000000 : ℝ), (15440164769081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266047029/625000000 : ℝ)|^4577 ≤ (8319862460741/25000000000000 : ℝ)^3553
        have hw : |(266047029/625000000 : ℝ)|=(266047029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450889513/1000000000 : ℝ)|^4577 ≤ (358402205997/1000000000000 : ℝ)^3553
        have hw : |(450889513/1000000000 : ℝ)|=(450889513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200827893/500000000 : ℝ)|^4577 ≤ (15440164769081/50000000000000 : ℝ)^3553
        have hw : |(200827893/500000000 : ℝ)|=(200827893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1540_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5487/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7767/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15899/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5319/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15899/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5319/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15899/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5319/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15899/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5319/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15899/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5319/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15899/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5319/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5319/50000 : ℝ) ^ (4575/1024 : ℝ) ≤ (4489840306616657/100000000000000000000 : ℝ) := by
    have hpowers : (5319/50000 : ℝ)^4575 ≤ (4489840306616657/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5319 : ℕ)^4575*100000000000000000000^1024 ≤ 4489840306616657^1024*50000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5319 50000 4489840306616657 100000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5319/50000 : ℝ)) (X := (4489840306616657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15899/100000 : ℝ) ^ (4575/1024 : ℝ) ≤ (27033435934899621/100000000000000000000 : ℝ) := by
    have hpowers : (15899/100000 : ℝ)^4575 ≤ (27033435934899621/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15899 : ℕ)^4575*100000000000000000000^1024 ≤ 27033435934899621^1024*100000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15899 100000 27033435934899621 100000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15899/100000 : ℝ)) (X := (27033435934899621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004489840306616657/50000000000000000000 : ℝ) ≤ (2000040196164029/2000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (50004489840306616657/50000000000000000000 : ℝ)^1024 ≤ (2000040196164029/2000000000000000 : ℝ)^4575 := by
      have hnat : (50004489840306616657 : ℕ)^1024*2000000000000000^4575 ≤ 2000040196164029^4575*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004489840306616657 50000000000000000000 2000040196164029 2000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000040196164029/2000000000000000 : ℝ)) (X := (50004489840306616657/50000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015761638120758139/50000000000000000000 : ℝ) ≤ (2500176370964819/2500000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (50015761638120758139/50000000000000000000 : ℝ)^1024 ≤ (2500176370964819/2500000000000000 : ℝ)^4575 := by
      have hnat : (50015761638120758139 : ℕ)^1024*2500000000000000^4575 ≤ 2500176370964819^4575*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015761638120758139 50000000000000000000 2500176370964819 2500000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500176370964819/2500000000000000 : ℝ)) (X := (50015761638120758139/50000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027033435934899621/50000000000000000000 : ℝ) ≤ (10001209986898407/10000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (50027033435934899621/50000000000000000000 : ℝ)^1024 ≤ (10001209986898407/10000000000000000 : ℝ)^4575 := by
      have hnat : (50027033435934899621 : ℕ)^1024*10000000000000000^4575 ≤ 10001209986898407^4575*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027033435934899621 50000000000000000000 10001209986898407 10000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001209986898407/10000000000000000 : ℝ)) (X := (50027033435934899621/50000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4489840306616657/100000000000000000000 : ℝ) ≤ ((52600323553434231689/52610000000000000000 : ℝ)+2*(504503039131/526100000000000 : ℝ)*(5319/50000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (52600323553434231689/52610000000000000000 : ℝ)+2*(504503039131/526100000000000 : ℝ)*(5319/50000 : ℝ)=(2000040196164029/2000000000000000 : ℝ) by norm_num, show 1+2*(4489840306616657/100000000000000000000 : ℝ)=(50004489840306616657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27033435934899621/100000000000000000000 : ℝ)+(4489840306616657/100000000000000000000 : ℝ) ≤ ((52600323553434231689/52610000000000000000 : ℝ)+(504503039131/526100000000000 : ℝ)*((15899/100000 : ℝ)+(5319/50000 : ℝ)))^(4575/1024 : ℝ) := by
    rw [show (52600323553434231689/52610000000000000000 : ℝ)+(504503039131/526100000000000 : ℝ)*((15899/100000 : ℝ)+(5319/50000 : ℝ))=(2500176370964819/2500000000000000 : ℝ) by norm_num, show 1+(27033435934899621/100000000000000000000 : ℝ)+(4489840306616657/100000000000000000000 : ℝ)=(50015761638120758139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27033435934899621/100000000000000000000 : ℝ) ≤ ((52600323553434231689/52610000000000000000 : ℝ)+2*(504503039131/526100000000000 : ℝ)*(15899/100000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (52600323553434231689/52610000000000000000 : ℝ)+2*(504503039131/526100000000000 : ℝ)*(15899/100000 : ℝ)=(10001209986898407/10000000000000000 : ℝ) by norm_num, show 1+2*(27033435934899621/100000000000000000000 : ℝ)=(50027033435934899621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52600323553434231689/52610000000000000000 : ℝ)*(X 1 0+X 2 0)+(504503039131/526100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (5319/50000 : ℝ)) (hi := (15899/100000 : ℝ)) (c := (52600323553434231689/52610000000000000000 : ℝ)) (alpha := (504503039131/526100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52600323553434231689/52610000000000000000 : ℝ)*(X 0 1+X 2 1)+(504503039131/526100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (5319/50000 : ℝ)) (hi := (15899/100000 : ℝ)) (c := (52600323553434231689/52610000000000000000 : ℝ)) (alpha := (504503039131/526100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52600323553434231689/52610000000000000000 : ℝ)*(X 0 2+X 1 2)+(504503039131/526100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (5319/50000 : ℝ)) (hi := (15899/100000 : ℝ)) (c := (52600323553434231689/52610000000000000000 : ℝ)) (alpha := (504503039131/526100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-913537469/5000000000 : ℝ)*X 0 0+(5431987827/10000000000 : ℝ)*X 0 1+(5216792441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350615683/10000000000 : ℝ)*X 1 0+(-484320261/2500000000 : ℝ)*X 1 1+(5216792847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350615879/10000000000 : ℝ)*X 2 0+(208671711/400000000 : ℝ)*X 2 1+(-1937280877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2128342327/5000000000 : ℝ)*X 0 0+(4013906567/10000000000 : ℝ)*X 0 1+(1127881439/2500000000 : ℝ)*X 0 2+(2128342327/5000000000 : ℝ)*X 1 0+(4013906567/10000000000 : ℝ)*X 1 1+(1127881439/2500000000 : ℝ)*X 1 2+(2128342327/5000000000 : ℝ)*X 2 0+(4013906567/10000000000 : ℝ)*X 2 1+(1127881439/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-22838797/125000000 : ℝ)*X 0 0+(5217930099/10000000000 : ℝ)*X 0 1+(5430842221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293897171/10000000000 : ℝ)*X 1 0+(-430807799/2500000000 : ℝ)*X 1 1+(5430842241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646948609/5000000000 : ℝ)*X 2 0+(5430842207/10000000000 : ℝ)*X 2 1+(-86161559/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((266047029/625000000 : ℝ)*X 0 0+(450889513/1000000000 : ℝ)*X 0 1+(200827893/500000000 : ℝ)*X 0 2+(266047029/625000000 : ℝ)*X 1 0+(450889513/1000000000 : ℝ)*X 1 1+(200827893/500000000 : ℝ)*X 1 2+(266047029/625000000 : ℝ)*X 2 0+(450889513/1000000000 : ℝ)*X 2 1+(200827893/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (536195070439519733367411423/131525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (722361569/50000000000000 : ℝ)*(base19) + (1241173691/100000000000000 : ℝ)*(base23) + (411663767/100000000000000 : ℝ)*(upper3) + (199992281/100000000000000 : ℝ)*(upper4) + (84826951/25000000000000 : ℝ)*(upper5) + (166414396599531/5000000000000 : ℝ)*(major0) + (166414396599531/5000000000000 : ℝ)*(major1) + (166414396599531/5000000000000 : ℝ)*(major2) + (4646958698864569/100000000000000 : ℝ)*(sp0) + (2323489560150117/50000000000000 : ℝ)*(sp1) + (4646979323849681/100000000000000 : ℝ)*(sp2) + (502395199564141/25000000000000 : ℝ)*(sp3) + (21866158803/100000000000000 : ℝ)*(sp4) + (1795601187/12500000000000 : ℝ)*(sp7) + (2009595163066061/100000000000000 : ℝ)*(f.failure) + (1161745141255843/25000000000000 : ℝ)*(f.sum) + (22374954172383/2630500000000000000000000000 : ℝ)*base65 + (2418279241528437859/263050000000000000000000000000000 : ℝ)*base67 + (927906682675962141/263050000000000000000000000000000 : ℝ)*base70 + (1817285356931737859/263050000000000000000000000000000 : ℝ)*base71 + (1194907922861/164406250000000000000000000 : ℝ)*base73 + (2495285321744262141/263050000000000000000000000000000 : ℝ)*base76 + (1591400434841887859/263050000000000000000000000000000 : ℝ)*base77 + (890026683397687859/263050000000000000000000000000000 : ℝ)*base79 + (14278434620717/5261000000000000000000000000 : ℝ)*base81 + (1469429/5000000000000000000000 : ℝ)*base90 + (1469429/5000000000000000000000 : ℝ)*base92 + (1469429/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4356818119078214229019787583/657625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253985121/25000000000000 : ℝ)*(base19) + (1173017407/100000000000000 : ℝ)*(base23) + (27376579/20000000000000 : ℝ)*(upper3) + (49123961/100000000000000 : ℝ)*(lower4) + (65420597/50000000000000 : ℝ)*(upper5) + (840987594514017/25000000000000 : ℝ)*(major0) + (840987594514017/25000000000000 : ℝ)*(major1) + (840987594514017/25000000000000 : ℝ)*(major2) + (7865237979/50000000000000 : ℝ)*(sp1) + (4459601041/25000000000000 : ℝ)*(sp2) + (4696772656116797/100000000000000 : ℝ)*(sp4) + (1174188977425089/25000000000000 : ℝ)*(sp5) + (2348376822347613/50000000000000 : ℝ)*(sp6) + (253890984894917/12500000000000 : ℝ)*(sp7) + (253890984894917/12500000000000 : ℝ)*(f.failure) + (4696772656116797/100000000000000 : ℝ)*(f.sum) + (44191244669553/6576250000000000000000000000 : ℝ)*base66 + (991582586368034713/1315250000000000000000000000000000 : ℝ)*base67 + (19037390620329534713/1315250000000000000000000000000000 : ℝ)*base69 + (423079569525284713/1315250000000000000000000000000000 : ℝ)*base71 + (35070252704863/6576250000000000000000000000 : ℝ)*base74 + (9090780817533284713/1315250000000000000000000000000000 : ℝ)*base75 + (6628351162006784713/1315250000000000000000000000000000 : ℝ)*base77 + (9183556737488284713/1315250000000000000000000000000000 : ℝ)*base79 + (3947263899631/3288125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3877613/625000000000000000000 : ℝ)*base90 + (3877613/625000000000000000000 : ℝ)*base92 + (3877613/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1540_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7767/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1540_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1540_s4_0 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-913696339/5000000000 : ℝ)*x 0 + (2714937443/5000000000 : ℝ)*x 1 + (326168443/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913696339/5000000000 : ℝ)^4577 ≤ (11196610004433/100000000000000 : ℝ)^3553 := by
    have hnat : (913696339 : ℕ)^4577*100000000000000^3553 ≤ 11196610004433^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913696339 5000000000 11196610004433 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714937443/5000000000 : ℝ)^4577 ≤ (22767972495069/50000000000000 : ℝ)^3553 := by
    have hnat : (2714937443 : ℕ)^4577*50000000000000^3553 ≤ 22767972495069^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714937443 5000000000 22767972495069 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326168443/625000000 : ℝ)^4577 ≤ (43267444996847/100000000000000 : ℝ)^3553 := by
    have hnat : (326168443 : ℕ)^4577*100000000000000^3553 ≤ 43267444996847^3553*625000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326168443 625000000 43267444996847 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-913696339/5000000000 : ℝ), (2714937443/5000000000 : ℝ), (326168443/625000000 : ℝ)] ![(11196610004433/100000000000000 : ℝ), (22767972495069/50000000000000 : ℝ), (43267444996847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-913696339/5000000000 : ℝ)|^4577 ≤ (11196610004433/100000000000000 : ℝ)^3553
        have hw : |(-913696339/5000000000 : ℝ)|=(913696339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714937443/5000000000 : ℝ)|^4577 ≤ (22767972495069/50000000000000 : ℝ)^3553
        have hw : |(2714937443/5000000000 : ℝ)|=(2714937443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326168443/625000000 : ℝ)|^4577 ≤ (43267444996847/100000000000000 : ℝ)^3553
        have hw : |(326168443/625000000 : ℝ)|=(326168443/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s4_1 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668757471/1250000000 : ℝ)*x 0 + (-1935495157/10000000000 : ℝ)*x 1 + (2609347447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668757471/1250000000 : ℝ)^4577 ≤ (44675523486927/100000000000000 : ℝ)^3553 := by
    have hnat : (668757471 : ℕ)^4577*100000000000000^3553 ≤ 44675523486927^3553*1250000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668757471 1250000000 44675523486927 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935495157/10000000000 : ℝ)^4577 ≤ (12057033577061/100000000000000 : ℝ)^3553 := by
    have hnat : (1935495157 : ℕ)^4577*100000000000000^3553 ≤ 12057033577061^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935495157 10000000000 12057033577061 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609347447/5000000000 : ℝ)^4577 ≤ (21633721462431/50000000000000 : ℝ)^3553 := by
    have hnat : (2609347447 : ℕ)^4577*50000000000000^3553 ≤ 21633721462431^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609347447 5000000000 21633721462431 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668757471/1250000000 : ℝ), (-1935495157/10000000000 : ℝ), (2609347447/5000000000 : ℝ)] ![(44675523486927/100000000000000 : ℝ), (12057033577061/100000000000000 : ℝ), (21633721462431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668757471/1250000000 : ℝ)|^4577 ≤ (44675523486927/100000000000000 : ℝ)^3553
        have hw : |(668757471/1250000000 : ℝ)|=(668757471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1935495157/10000000000 : ℝ)|^4577 ≤ (12057033577061/100000000000000 : ℝ)^3553
        have hw : |(-1935495157/10000000000 : ℝ)|=(1935495157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609347447/5000000000 : ℝ)|^4577 ≤ (21633721462431/50000000000000 : ℝ)^3553
        have hw : |(2609347447/5000000000 : ℝ)|=(2609347447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s4_2 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675029929/5000000000 : ℝ)*x 0 + (1043738979/2000000000 : ℝ)*x 1 + (-387099007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675029929/5000000000 : ℝ)^4577 ≤ (44675524455069/100000000000000 : ℝ)^3553 := by
    have hnat : (2675029929 : ℕ)^4577*100000000000000^3553 ≤ 44675524455069^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675029929 5000000000 44675524455069 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043738979/2000000000 : ℝ)^4577 ≤ (21633721467771/50000000000000 : ℝ)^3553 := by
    have hnat : (1043738979 : ℕ)^4577*50000000000000^3553 ≤ 21633721467771^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043738979 2000000000 21633721467771 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387099007/2000000000 : ℝ)^4577 ≤ (3014258149509/25000000000000 : ℝ)^3553 := by
    have hnat : (387099007 : ℕ)^4577*25000000000000^3553 ≤ 3014258149509^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387099007 2000000000 3014258149509 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675029929/5000000000 : ℝ), (1043738979/2000000000 : ℝ), (-387099007/2000000000 : ℝ)] ![(44675524455069/100000000000000 : ℝ), (21633721467771/50000000000000 : ℝ), (3014258149509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675029929/5000000000 : ℝ)|^4577 ≤ (44675524455069/100000000000000 : ℝ)^3553
        have hw : |(2675029929/5000000000 : ℝ)|=(2675029929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043738979/2000000000 : ℝ)|^4577 ≤ (21633721467771/50000000000000 : ℝ)^3553
        have hw : |(1043738979/2000000000 : ℝ)|=(1043738979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387099007/2000000000 : ℝ)|^4577 ≤ (3014258149509/25000000000000 : ℝ)^3553
        have hw : |(-387099007/2000000000 : ℝ)|=(387099007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s4_3 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425688397/1000000000 : ℝ)*x 0 + (160741119/400000000 : ℝ)*x 1 + (563357497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425688397/1000000000 : ℝ)^4577 ≤ (33280774278877/100000000000000 : ℝ)^3553 := by
    have hnat : (425688397 : ℕ)^4577*100000000000000^3553 ≤ 33280774278877^3553*1000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425688397 1000000000 33280774278877 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160741119/400000000 : ℝ)^4577 ≤ (3862480383707/12500000000000 : ℝ)^3553 := by
    have hnat : (160741119 : ℕ)^4577*12500000000000^3553 ≤ 3862480383707^3553*400000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160741119 400000000 3862480383707 12500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563357497/1250000000 : ℝ)^4577 ≤ (35819382636311/100000000000000 : ℝ)^3553 := by
    have hnat : (563357497 : ℕ)^4577*100000000000000^3553 ≤ 35819382636311^3553*1250000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563357497 1250000000 35819382636311 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425688397/1000000000 : ℝ), (160741119/400000000 : ℝ), (563357497/1250000000 : ℝ)] ![(33280774278877/100000000000000 : ℝ), (3862480383707/12500000000000 : ℝ), (35819382636311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425688397/1000000000 : ℝ)|^4577 ≤ (33280774278877/100000000000000 : ℝ)^3553
        have hw : |(425688397/1000000000 : ℝ)|=(425688397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160741119/400000000 : ℝ)|^4577 ≤ (3862480383707/12500000000000 : ℝ)^3553
        have hw : |(160741119/400000000 : ℝ)|=(160741119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563357497/1250000000 : ℝ)|^4577 ≤ (35819382636311/100000000000000 : ℝ)^3553
        have hw : |(563357497/1250000000 : ℝ)|=(563357497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s4_4 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-913710279/5000000000 : ℝ)*x 0 + (2609895369/5000000000 : ℝ)*x 1 + (1085754251/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913710279/5000000000 : ℝ)^4577 ≤ (11196830060881/100000000000000 : ℝ)^3553 := by
    have hnat : (913710279 : ℕ)^4577*100000000000000^3553 ≤ 11196830060881^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913710279 5000000000 11196830060881 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609895369/5000000000 : ℝ)^4577 ≤ (5409893408017/12500000000000 : ℝ)^3553 := by
    have hnat : (2609895369 : ℕ)^4577*12500000000000^3553 ≤ 5409893408017^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609895369 5000000000 5409893408017 12500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085754251/2000000000 : ℝ)^4577 ≤ (45524022652801/100000000000000 : ℝ)^3553 := by
    have hnat : (1085754251 : ℕ)^4577*100000000000000^3553 ≤ 45524022652801^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085754251 2000000000 45524022652801 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-913710279/5000000000 : ℝ), (2609895369/5000000000 : ℝ), (1085754251/2000000000 : ℝ)] ![(11196830060881/100000000000000 : ℝ), (5409893408017/12500000000000 : ℝ), (45524022652801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-913710279/5000000000 : ℝ)|^4577 ≤ (11196830060881/100000000000000 : ℝ)^3553
        have hw : |(-913710279/5000000000 : ℝ)|=(913710279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609895369/5000000000 : ℝ)|^4577 ≤ (5409893408017/12500000000000 : ℝ)^3553
        have hw : |(2609895369/5000000000 : ℝ)|=(2609895369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085754251/2000000000 : ℝ)|^4577 ≤ (45524022652801/100000000000000 : ℝ)^3553
        have hw : |(1085754251/2000000000 : ℝ)|=(1085754251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s4_5 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647200009/5000000000 : ℝ)*x 0 + (-215677351/1250000000 : ℝ)*x 1 + (2714385627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647200009/5000000000 : ℝ)^4577 ≤ (8815536750511/20000000000000 : ℝ)^3553 := by
    have hnat : (2647200009 : ℕ)^4577*20000000000000^3553 ≤ 8815536750511^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647200009 5000000000 8815536750511 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215677351/1250000000 : ℝ)^4577 ≤ (2079658717947/20000000000000 : ℝ)^3553 := by
    have hnat : (215677351 : ℕ)^4577*20000000000000^3553 ≤ 2079658717947^3553*1250000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215677351 1250000000 2079658717947 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714385627/5000000000 : ℝ)^4577 ≤ (22762011320999/50000000000000 : ℝ)^3553 := by
    have hnat : (2714385627 : ℕ)^4577*50000000000000^3553 ≤ 22762011320999^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714385627 5000000000 22762011320999 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647200009/5000000000 : ℝ), (-215677351/1250000000 : ℝ), (2714385627/5000000000 : ℝ)] ![(8815536750511/20000000000000 : ℝ), (2079658717947/20000000000000 : ℝ), (22762011320999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647200009/5000000000 : ℝ)|^4577 ≤ (8815536750511/20000000000000 : ℝ)^3553
        have hw : |(2647200009/5000000000 : ℝ)|=(2647200009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215677351/1250000000 : ℝ)|^4577 ≤ (2079658717947/20000000000000 : ℝ)^3553
        have hw : |(-215677351/1250000000 : ℝ)|=(215677351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714385627/5000000000 : ℝ)|^4577 ≤ (22762011320999/50000000000000 : ℝ)^3553
        have hw : |(2714385627/5000000000 : ℝ)|=(2714385627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s4_6 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647200007/5000000000 : ℝ)*x 0 + (5428771253/10000000000 : ℝ)*x 1 + (-345083763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647200007/5000000000 : ℝ)^4577 ≤ (5509710463707/12500000000000 : ℝ)^3553 := by
    have hnat : (2647200007 : ℕ)^4577*12500000000000^3553 ≤ 5509710463707^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647200007 5000000000 5509710463707 12500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428771253/10000000000 : ℝ)^4577 ≤ (11381005657799/25000000000000 : ℝ)^3553 := by
    have hnat : (5428771253 : ℕ)^4577*25000000000000^3553 ≤ 11381005657799^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428771253 10000000000 11381005657799 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345083763/2000000000 : ℝ)^4577 ≤ (10398293644079/100000000000000 : ℝ)^3553 := by
    have hnat : (345083763 : ℕ)^4577*100000000000000^3553 ≤ 10398293644079^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345083763 2000000000 10398293644079 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647200007/5000000000 : ℝ), (5428771253/10000000000 : ℝ), (-345083763/2000000000 : ℝ)] ![(5509710463707/12500000000000 : ℝ), (11381005657799/25000000000000 : ℝ), (10398293644079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647200007/5000000000 : ℝ)|^4577 ≤ (5509710463707/12500000000000 : ℝ)^3553
        have hw : |(2647200007/5000000000 : ℝ)|=(2647200007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428771253/10000000000 : ℝ)|^4577 ≤ (11381005657799/25000000000000 : ℝ)^3553
        have hw : |(5428771253/10000000000 : ℝ)|=(5428771253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345083763/2000000000 : ℝ)|^4577 ≤ (10398293644079/100000000000000 : ℝ)^3553
        have hw : |(-345083763/2000000000 : ℝ)|=(345083763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s4_7 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851389779/2000000000 : ℝ)*x 0 + (4504326259/10000000000 : ℝ)*x 1 + (4021080381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851389779/2000000000 : ℝ)^4577 ≤ (33281428162149/100000000000000 : ℝ)^3553 := by
    have hnat : (851389779 : ℕ)^4577*100000000000000^3553 ≤ 33281428162149^3553*2000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851389779 2000000000 33281428162149 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504326259/10000000000 : ℝ)^4577 ≤ (35793443670813/100000000000000 : ℝ)^3553 := by
    have hnat : (4504326259 : ℕ)^4577*100000000000000^3553 ≤ 35793443670813^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504326259 10000000000 35793443670813 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021080381/10000000000 : ℝ)^4577 ≤ (15462564079199/50000000000000 : ℝ)^3553 := by
    have hnat : (4021080381 : ℕ)^4577*50000000000000^3553 ≤ 15462564079199^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021080381 10000000000 15462564079199 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851389779/2000000000 : ℝ), (4504326259/10000000000 : ℝ), (4021080381/10000000000 : ℝ)] ![(33281428162149/100000000000000 : ℝ), (35793443670813/100000000000000 : ℝ), (15462564079199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851389779/2000000000 : ℝ)|^4577 ≤ (33281428162149/100000000000000 : ℝ)^3553
        have hw : |(851389779/2000000000 : ℝ)|=(851389779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504326259/10000000000 : ℝ)|^4577 ≤ (35793443670813/100000000000000 : ℝ)^3553
        have hw : |(4504326259/10000000000 : ℝ)|=(4504326259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021080381/10000000000 : ℝ)|^4577 ≤ (15462564079199/50000000000000 : ℝ)^3553
        have hw : |(4021080381/10000000000 : ℝ)|=(4021080381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1540_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7767/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2203/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7767/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7767/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5487/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7767/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7767/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5487/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7767/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7767/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5487/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5487/50000 : ℝ) ^ (4575/1024 : ℝ) ≤ (2579514921444219/50000000000000000000 : ℝ) := by
    have hpowers : (5487/50000 : ℝ)^4575 ≤ (2579514921444219/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5487 : ℕ)^4575*50000000000000000000^1024 ≤ 2579514921444219^1024*50000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5487 50000 2579514921444219 50000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5487/50000 : ℝ)) (X := (2579514921444219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7767/50000 : ℝ) ^ (4575/1024 : ℝ) ≤ (24368961001295829/100000000000000000000 : ℝ) := by
    have hpowers : (7767/50000 : ℝ)^4575 ≤ (24368961001295829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7767 : ℕ)^4575*100000000000000000000^1024 ≤ 24368961001295829^1024*50000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7767 50000 24368961001295829 100000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7767/50000 : ℝ)) (X := (24368961001295829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002579514921444219/25000000000000000000 : ℝ) ≤ (10000230934864723/10000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (25002579514921444219/25000000000000000000 : ℝ)^1024 ≤ (10000230934864723/10000000000000000 : ℝ)^4575 := by
      have hnat : (25002579514921444219 : ℕ)^1024*10000000000000000^4575 ≤ 10000230934864723^4575*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002579514921444219 25000000000000000000 10000230934864723 10000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000230934864723/10000000000000000 : ℝ)) (X := (25002579514921444219/25000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029527990844184267/100000000000000000000 : ℝ) ≤ (5000330417467511/5000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (100029527990844184267/100000000000000000000 : ℝ)^1024 ≤ (5000330417467511/5000000000000000 : ℝ)^4575 := by
      have hnat : (100029527990844184267 : ℕ)^1024*5000000000000000^4575 ≤ 5000330417467511^4575*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029527990844184267 100000000000000000000 5000330417467511 5000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000330417467511/5000000000000000 : ℝ)) (X := (100029527990844184267/100000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024368961001295829/50000000000000000000 : ℝ) ≤ (10001090735005321/10000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (50024368961001295829/50000000000000000000 : ℝ)^1024 ≤ (10001090735005321/10000000000000000 : ℝ)^4575 := by
      have hnat : (50024368961001295829 : ℕ)^1024*10000000000000000^4575 ≤ 10001090735005321^4575*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024368961001295829 50000000000000000000 10001090735005321 10000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001090735005321/10000000000000000 : ℝ)) (X := (50024368961001295829/50000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2579514921444219/50000000000000000000 : ℝ) ≤ ((3799301468020017869/3800000000000000000 : ℝ)+2*(143300023433/152000000000000 : ℝ)*(5487/50000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (3799301468020017869/3800000000000000000 : ℝ)+2*(143300023433/152000000000000 : ℝ)*(5487/50000 : ℝ)=(10000230934864723/10000000000000000 : ℝ) by norm_num, show 1+2*(2579514921444219/50000000000000000000 : ℝ)=(25002579514921444219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24368961001295829/100000000000000000000 : ℝ)+(2579514921444219/50000000000000000000 : ℝ) ≤ ((3799301468020017869/3800000000000000000 : ℝ)+(143300023433/152000000000000 : ℝ)*((7767/50000 : ℝ)+(5487/50000 : ℝ)))^(4575/1024 : ℝ) := by
    rw [show (3799301468020017869/3800000000000000000 : ℝ)+(143300023433/152000000000000 : ℝ)*((7767/50000 : ℝ)+(5487/50000 : ℝ))=(5000330417467511/5000000000000000 : ℝ) by norm_num, show 1+(24368961001295829/100000000000000000000 : ℝ)+(2579514921444219/50000000000000000000 : ℝ)=(100029527990844184267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24368961001295829/100000000000000000000 : ℝ) ≤ ((3799301468020017869/3800000000000000000 : ℝ)+2*(143300023433/152000000000000 : ℝ)*(7767/50000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (3799301468020017869/3800000000000000000 : ℝ)+2*(143300023433/152000000000000 : ℝ)*(7767/50000 : ℝ)=(10001090735005321/10000000000000000 : ℝ) by norm_num, show 1+2*(24368961001295829/100000000000000000000 : ℝ)=(50024368961001295829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3799301468020017869/3800000000000000000 : ℝ)*(X 1 0+X 2 0)+(143300023433/152000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (7767/50000 : ℝ)) (c := (3799301468020017869/3800000000000000000 : ℝ)) (alpha := (143300023433/152000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3799301468020017869/3800000000000000000 : ℝ)*(X 0 1+X 2 1)+(143300023433/152000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (7767/50000 : ℝ)) (c := (3799301468020017869/3800000000000000000 : ℝ)) (alpha := (143300023433/152000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3799301468020017869/3800000000000000000 : ℝ)*(X 0 2+X 1 2)+(143300023433/152000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (5487/50000 : ℝ)) (hi := (7767/50000 : ℝ)) (c := (3799301468020017869/3800000000000000000 : ℝ)) (alpha := (143300023433/152000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-913696339/5000000000 : ℝ)*X 0 0+(2714937443/5000000000 : ℝ)*X 0 1+(326168443/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668757471/1250000000 : ℝ)*X 1 0+(-1935495157/10000000000 : ℝ)*X 1 1+(2609347447/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675029929/5000000000 : ℝ)*X 2 0+(1043738979/2000000000 : ℝ)*X 2 1+(-387099007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((425688397/1000000000 : ℝ)*X 0 0+(160741119/400000000 : ℝ)*X 0 1+(563357497/1250000000 : ℝ)*X 0 2+(425688397/1000000000 : ℝ)*X 1 0+(160741119/400000000 : ℝ)*X 1 1+(563357497/1250000000 : ℝ)*X 1 2+(425688397/1000000000 : ℝ)*X 2 0+(160741119/400000000 : ℝ)*X 2 1+(563357497/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-913710279/5000000000 : ℝ)*X 0 0+(2609895369/5000000000 : ℝ)*X 0 1+(1085754251/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647200009/5000000000 : ℝ)*X 1 0+(-215677351/1250000000 : ℝ)*X 1 1+(2714385627/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647200007/5000000000 : ℝ)*X 2 0+(5428771253/10000000000 : ℝ)*X 2 1+(-345083763/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((851389779/2000000000 : ℝ)*X 0 0+(4504326259/10000000000 : ℝ)*X 0 1+(4021080381/10000000000 : ℝ)*X 0 2+(851389779/2000000000 : ℝ)*X 1 0+(4504326259/10000000000 : ℝ)*X 1 1+(4021080381/10000000000 : ℝ)*X 1 2+(851389779/2000000000 : ℝ)*X 2 0+(4504326259/10000000000 : ℝ)*X 2 1+(4021080381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12762302504086431963285831/5000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381273491/50000000000000 : ℝ)*(base19) + (178444449/25000000000000 : ℝ)*(base23) + (65452489/100000000000000 : ℝ)*(upper3) + (34354831/50000000000000 : ℝ)*(upper4) + (54131587/50000000000000 : ℝ)*(upper5) + (423944677735307/12500000000000 : ℝ)*(major0) + (423944677735307/12500000000000 : ℝ)*(major1) + (1695778710941229/50000000000000 : ℝ)*(major2) + (1183827021927881/25000000000000 : ℝ)*(sp0) + (2367658596014829/50000000000000 : ℝ)*(sp1) + (947063448159769/20000000000000 : ℝ)*(sp2) + (1023895949238977/50000000000000 : ℝ)*(sp3) + (2466716279/25000000000000 : ℝ)*(sp4) + (2452814147/50000000000000 : ℝ)*(sp7) + (255974600513281/12500000000000 : ℝ)*(f.failure) + (3699467152013/78125000000 : ℝ)*(f.sum) + (3291077861119/7600000000000000000000000000 : ℝ)*base66 + (415282575518067967/47500000000000000000000000000000 : ℝ)*base68 + (953532203381921001/190000000000000000000000000000000 : ℝ)*base69 + (441237273103067967/47500000000000000000000000000000 : ℝ)*base72 + (3638507290881/7600000000000000000000000000 : ℝ)*base73 + (661249206981921001/190000000000000000000000000000000 : ℝ)*base75 + (15666814204448643/2500000000000000000000000000000 : ℝ)*base78 + (29781401831948643/2500000000000000000000000000000 : ℝ)*base80 + (3537581366919/950000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3927991/625000000000000000000 : ℝ)*base89 + (3927991/625000000000000000000 : ℝ)*base91 + (8572009/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151461890990226142533615483/19000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20039323/1562500000000 : ℝ)*(base19) + (1407630693/100000000000000 : ℝ)*(base23) + (168643633/100000000000000 : ℝ)*(upper3) + (28822761/50000000000000 : ℝ)*(lower4) + (6239043/4000000000000 : ℝ)*(upper5) + (685447367628631/20000000000000 : ℝ)*(major0) + (685447367628631/20000000000000 : ℝ)*(major1) + (685447367628631/20000000000000 : ℝ)*(major2) + (4964213507/25000000000000 : ℝ)*(sp1) + (21744877751/100000000000000 : ℝ)*(sp2) + (957026728777641/20000000000000 : ℝ)*(sp4) + (957022500903501/20000000000000 : ℝ)*(sp5) + (4785110491379761/100000000000000 : ℝ)*(sp6) + (1034669883337743/50000000000000 : ℝ)*(sp7) + (1034669883337743/50000000000000 : ℝ)*(f.failure) + (957026728777641/20000000000000 : ℝ)*(f.sum) + (11454524051377/1520000000000000000000000000 : ℝ)*base66 + (8449073214083281/4000000000000000000000000000000 : ℝ)*base67 + (4297252106083281/4000000000000000000000000000000 : ℝ)*base69 + (22632992385916719/4000000000000000000000000000000 : ℝ)*base72 + (2075541844463/1520000000000000000000000000 : ℝ)*base73 + (6804503998083281/4000000000000000000000000000000 : ℝ)*base75 + (23545905942083281/4000000000000000000000000000000 : ℝ)*base77 + (10052487662083281/4000000000000000000000000000000 : ℝ)*base79 + (3224637702097/1520000000000000000000000000 : ℝ)*base82 + (5770873/2500000000000000000000 : ℝ)*base89 + (5770873/2500000000000000000000 : ℝ)*base91 + (5770873/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1540_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7767/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1540_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1540_s5_0 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73097101/400000000 : ℝ)*x 0 + (5429638429/10000000000 : ℝ)*x 1 + (1304727127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73097101/400000000 : ℝ)^4577 ≤ (5598442525733/50000000000000 : ℝ)^3553 := by
    have hnat : (73097101 : ℕ)^4577*50000000000000^3553 ≤ 5598442525733^3553*400000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73097101 400000000 5598442525733 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429638429/10000000000 : ℝ)^4577 ≤ (45533390526731/100000000000000 : ℝ)^3553 := by
    have hnat : (5429638429 : ℕ)^4577*100000000000000^3553 ≤ 45533390526731^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429638429 10000000000 45533390526731 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304727127/2500000000 : ℝ)^4577 ≤ (216348622041/500000000000 : ℝ)^3553 := by
    have hnat : (1304727127 : ℕ)^4577*500000000000^3553 ≤ 216348622041^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304727127 2500000000 216348622041 500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73097101/400000000 : ℝ), (5429638429/10000000000 : ℝ), (1304727127/2500000000 : ℝ)] ![(5598442525733/50000000000000 : ℝ), (45533390526731/100000000000000 : ℝ), (216348622041/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73097101/400000000 : ℝ)|^4577 ≤ (5598442525733/50000000000000 : ℝ)^3553
        have hw : |(-73097101/400000000 : ℝ)|=(73097101/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429638429/10000000000 : ℝ)|^4577 ≤ (45533390526731/100000000000000 : ℝ)^3553
        have hw : |(5429638429/10000000000 : ℝ)|=(5429638429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304727127/2500000000 : ℝ)|^4577 ≤ (216348622041/500000000000 : ℝ)^3553
        have hw : |(1304727127/2500000000 : ℝ)|=(1304727127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s5_1 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349997507/10000000000 : ℝ)*x 0 + (-1935294309/10000000000 : ℝ)*x 1 + (1304727127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349997507/10000000000 : ℝ)^4577 ≤ (4467485373791/10000000000000 : ℝ)^3553 := by
    have hnat : (5349997507 : ℕ)^4577*10000000000000^3553 ≤ 4467485373791^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349997507 10000000000 4467485373791 10000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935294309/10000000000 : ℝ)^4577 ≤ (602771091831/5000000000000 : ℝ)^3553 := by
    have hnat : (1935294309 : ℕ)^4577*5000000000000^3553 ≤ 602771091831^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935294309 10000000000 602771091831 5000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304727127/2500000000 : ℝ)^4577 ≤ (216348622041/500000000000 : ℝ)^3553 := by
    have hnat : (1304727127 : ℕ)^4577*500000000000^3553 ≤ 216348622041^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304727127 2500000000 216348622041 500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349997507/10000000000 : ℝ), (-1935294309/10000000000 : ℝ), (1304727127/2500000000 : ℝ)] ![(4467485373791/10000000000000 : ℝ), (602771091831/5000000000000 : ℝ), (216348622041/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349997507/10000000000 : ℝ)|^4577 ≤ (4467485373791/10000000000000 : ℝ)^3553
        have hw : |(5349997507/10000000000 : ℝ)|=(5349997507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1935294309/10000000000 : ℝ)|^4577 ≤ (602771091831/5000000000000 : ℝ)^3553
        have hw : |(-1935294309/10000000000 : ℝ)|=(1935294309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304727127/2500000000 : ℝ)|^4577 ≤ (216348622041/500000000000 : ℝ)^3553
        have hw : |(1304727127/2500000000 : ℝ)|=(1304727127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s5_2 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674998771/5000000000 : ℝ)*x 0 + (652363559/1250000000 : ℝ)*x 1 + (-1935294311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674998771/5000000000 : ℝ)^4577 ≤ (5584356764301/12500000000000 : ℝ)^3553 := by
    have hnat : (2674998771 : ℕ)^4577*12500000000000^3553 ≤ 5584356764301^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674998771 5000000000 5584356764301 12500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652363559/1250000000 : ℝ)^4577 ≤ (43269724023703/100000000000000 : ℝ)^3553 := by
    have hnat : (652363559 : ℕ)^4577*100000000000000^3553 ≤ 43269724023703^3553*1250000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652363559 1250000000 43269724023703 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935294311/10000000000 : ℝ)^4577 ≤ (12055421852669/100000000000000 : ℝ)^3553 := by
    have hnat : (1935294311 : ℕ)^4577*100000000000000^3553 ≤ 12055421852669^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935294311 10000000000 12055421852669 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674998771/5000000000 : ℝ), (652363559/1250000000 : ℝ), (-1935294311/10000000000 : ℝ)] ![(5584356764301/12500000000000 : ℝ), (43269724023703/100000000000000 : ℝ), (12055421852669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674998771/5000000000 : ℝ)|^4577 ≤ (5584356764301/12500000000000 : ℝ)^3553
        have hw : |(2674998771/5000000000 : ℝ)|=(2674998771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652363559/1250000000 : ℝ)|^4577 ≤ (43269724023703/100000000000000 : ℝ)^3553
        have hw : |(652363559/1250000000 : ℝ)|=(652363559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1935294311/10000000000 : ℝ)|^4577 ≤ (12055421852669/100000000000000 : ℝ)^3553
        have hw : |(-1935294311/10000000000 : ℝ)|=(1935294311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s5_3 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4256906211/10000000000 : ℝ)*x 0 + (4019045903/10000000000 : ℝ)*x 1 + (4506336991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256906211/10000000000 : ℝ)^4577 ≤ (8320249568937/25000000000000 : ℝ)^3553 := by
    have hnat : (4256906211 : ℕ)^4577*25000000000000^3553 ≤ 8320249568937^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256906211 10000000000 8320249568937 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4019045903/10000000000 : ℝ)^4577 ≤ (7726243370993/25000000000000 : ℝ)^3553 := by
    have hnat : (4019045903 : ℕ)^4577*25000000000000^3553 ≤ 7726243370993^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019045903 10000000000 7726243370993 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506336991/10000000000 : ℝ)^4577 ≤ (8953507056321/25000000000000 : ℝ)^3553 := by
    have hnat : (4506336991 : ℕ)^4577*25000000000000^3553 ≤ 8953507056321^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506336991 10000000000 8953507056321 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256906211/10000000000 : ℝ), (4019045903/10000000000 : ℝ), (4506336991/10000000000 : ℝ)] ![(8320249568937/25000000000000 : ℝ), (7726243370993/25000000000000 : ℝ), (8953507056321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256906211/10000000000 : ℝ)|^4577 ≤ (8320249568937/25000000000000 : ℝ)^3553
        have hw : |(4256906211/10000000000 : ℝ)|=(4256906211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4019045903/10000000000 : ℝ)|^4577 ≤ (7726243370993/25000000000000 : ℝ)^3553
        have hw : |(4019045903/10000000000 : ℝ)|=(4019045903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506336991/10000000000 : ℝ)|^4577 ≤ (8953507056321/25000000000000 : ℝ)^3553
        have hw : |(4506336991/10000000000 : ℝ)|=(4506336991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s5_4 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-913727697/5000000000 : ℝ)*x 0 + (5219999637/10000000000 : ℝ)*x 1 + (21714157/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913727697/5000000000 : ℝ)^4577 ≤ (111971050223/1000000000000 : ℝ)^3553 := by
    have hnat : (913727697 : ℕ)^4577*1000000000000^3553 ≤ 111971050223^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913727697 5000000000 111971050223 1000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219999637/10000000000 : ℝ)^4577 ≤ (21640689262051/50000000000000 : ℝ)^3553 := by
    have hnat : (5219999637 : ℕ)^4577*50000000000000^3553 ≤ 21640689262051^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219999637 10000000000 21640689262051 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21714157/40000000 : ℝ)^4577 ≤ (22760758215617/50000000000000 : ℝ)^3553 := by
    have hnat : (21714157 : ℕ)^4577*50000000000000^3553 ≤ 22760758215617^3553*40000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21714157 40000000 22760758215617 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-913727697/5000000000 : ℝ), (5219999637/10000000000 : ℝ), (21714157/40000000 : ℝ)] ![(111971050223/1000000000000 : ℝ), (21640689262051/50000000000000 : ℝ), (22760758215617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-913727697/5000000000 : ℝ)|^4577 ≤ (111971050223/1000000000000 : ℝ)^3553
        have hw : |(-913727697/5000000000 : ℝ)|=(913727697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219999637/10000000000 : ℝ)|^4577 ≤ (21640689262051/50000000000000 : ℝ)^3553
        have hw : |(5219999637/10000000000 : ℝ)|=(5219999637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21714157/40000000 : ℝ)|^4577 ≤ (22760758215617/50000000000000 : ℝ)^3553
        have hw : |(21714157/40000000 : ℝ)|=(21714157/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s5_5 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294456469/10000000000 : ℝ)*x 0 + (-862831791/5000000000 : ℝ)*x 1 + (5428539293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294456469/10000000000 : ℝ)^4577 ≤ (22039144588551/50000000000000 : ℝ)^3553 := by
    have hnat : (5294456469 : ℕ)^4577*50000000000000^3553 ≤ 22039144588551^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294456469 10000000000 22039144588551 50000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862831791/5000000000 : ℝ)^4577 ≤ (2080038782539/20000000000000 : ℝ)^3553 := by
    have hnat : (862831791 : ℕ)^4577*20000000000000^3553 ≤ 2080038782539^3553*5000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862831791 5000000000 2080038782539 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428539293/10000000000 : ℝ)^4577 ≤ (5690189611967/12500000000000 : ℝ)^3553 := by
    have hnat : (5428539293 : ℕ)^4577*12500000000000^3553 ≤ 5690189611967^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428539293 10000000000 5690189611967 12500000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294456469/10000000000 : ℝ), (-862831791/5000000000 : ℝ), (5428539293/10000000000 : ℝ)] ![(22039144588551/50000000000000 : ℝ), (2080038782539/20000000000000 : ℝ), (5690189611967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294456469/10000000000 : ℝ)|^4577 ≤ (22039144588551/50000000000000 : ℝ)^3553
        have hw : |(5294456469/10000000000 : ℝ)|=(5294456469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-862831791/5000000000 : ℝ)|^4577 ≤ (2080038782539/20000000000000 : ℝ)^3553
        have hw : |(-862831791/5000000000 : ℝ)|=(862831791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428539293/10000000000 : ℝ)|^4577 ≤ (5690189611967/12500000000000 : ℝ)^3553
        have hw : |(5428539293/10000000000 : ℝ)|=(5428539293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s5_6 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294456511/10000000000 : ℝ)*x 0 + (217141571/400000000 : ℝ)*x 1 + (-1725663549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294456511/10000000000 : ℝ)^4577 ≤ (44078289627543/100000000000000 : ℝ)^3553 := by
    have hnat : (5294456511 : ℕ)^4577*100000000000000^3553 ≤ 44078289627543^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294456511 10000000000 44078289627543 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217141571/400000000 : ℝ)^4577 ≤ (45521516701293/100000000000000 : ℝ)^3553 := by
    have hnat : (217141571 : ℕ)^4577*100000000000000^3553 ≤ 45521516701293^3553*400000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217141571 400000000 45521516701293 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1725663549/10000000000 : ℝ)^4577 ≤ (10400193656491/100000000000000 : ℝ)^3553 := by
    have hnat : (1725663549 : ℕ)^4577*100000000000000^3553 ≤ 10400193656491^3553*10000000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725663549 10000000000 10400193656491 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294456511/10000000000 : ℝ), (217141571/400000000 : ℝ), (-1725663549/10000000000 : ℝ)] ![(44078289627543/100000000000000 : ℝ), (45521516701293/100000000000000 : ℝ), (10400193656491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294456511/10000000000 : ℝ)|^4577 ≤ (44078289627543/100000000000000 : ℝ)^3553
        have hw : |(5294456511/10000000000 : ℝ)|=(5294456511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217141571/400000000 : ℝ)|^4577 ≤ (45521516701293/100000000000000 : ℝ)^3553
        have hw : |(217141571/400000000 : ℝ)|=(217141571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1725663549/10000000000 : ℝ)|^4577 ≤ (10400193656491/100000000000000 : ℝ)^3553
        have hw : |(-1725663549/10000000000 : ℝ)|=(1725663549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1540_s5_7 (p : ℝ) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266060669/625000000 : ℝ)*x 0 + (1125953493/2500000000 : ℝ)*x 1 + (502698439/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266060669/625000000 : ℝ)^4577 ≤ (33281647809159/100000000000000 : ℝ)^3553 := by
    have hnat : (266060669 : ℕ)^4577*100000000000000^3553 ≤ 33281647809159^3553*625000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266060669 625000000 33281647809159 100000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125953493/2500000000 : ℝ)^4577 ≤ (8947049909001/25000000000000 : ℝ)^3553 := by
    have hnat : (1125953493 : ℕ)^4577*25000000000000^3553 ≤ 8947049909001^3553*2500000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125953493 2500000000 8947049909001 25000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502698439/1250000000 : ℝ)^4577 ≤ (6186030507753/20000000000000 : ℝ)^3553 := by
    have hnat : (502698439 : ℕ)^4577*20000000000000^3553 ≤ 6186030507753^3553*1250000000^4577 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502698439 1250000000 6186030507753 20000000000000 4577 3553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4577/1024 : ℝ)) 4577 3553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266060669/625000000 : ℝ), (1125953493/2500000000 : ℝ), (502698439/1250000000 : ℝ)] ![(33281647809159/100000000000000 : ℝ), (8947049909001/25000000000000 : ℝ), (6186030507753/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266060669/625000000 : ℝ)|^4577 ≤ (33281647809159/100000000000000 : ℝ)^3553
        have hw : |(266060669/625000000 : ℝ)|=(266060669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125953493/2500000000 : ℝ)|^4577 ≤ (8947049909001/25000000000000 : ℝ)^3553
        have hw : |(1125953493/2500000000 : ℝ)|=(1125953493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502698439/1250000000 : ℝ)|^4577 ≤ (6186030507753/20000000000000 : ℝ)^3553
        have hw : |(502698439/1250000000 : ℝ)|=(502698439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1540_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11019/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2203/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2203/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2203/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2203/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2203/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2203/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2203/20000 : ℝ) ^ (4575/1024 : ℝ) ≤ (327856516663323/6250000000000000000 : ℝ) := by
    have hpowers : (2203/20000 : ℝ)^4575 ≤ (327856516663323/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2203 : ℕ)^4575*6250000000000000000^1024 ≤ 327856516663323^1024*20000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2203 20000 327856516663323 6250000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2203/20000 : ℝ)) (X := (327856516663323/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4575/1024 : ℝ) ≤ (12031041998739289/50000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4575 ≤ (12031041998739289/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4575*50000000000000000000^1024 ≤ 12031041998739289^1024*10000^4575 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 12031041998739289 50000000000000000000 4575 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (12031041998739289/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125327856516663323/3125000000000000000 : ℝ) ≤ (2000046962906871/2000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (3125327856516663323/3125000000000000000 : ℝ)^1024 ≤ (2000046962906871/2000000000000000 : ℝ)^4575 := by
      have hnat : (3125327856516663323 : ℕ)^1024*2000000000000000^4575 ≤ 2000046962906871^4575*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125327856516663323 3125000000000000000 2000046962906871 2000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000046962906871/2000000000000000 : ℝ)) (X := (3125327856516663323/3125000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014653894132045873/50000000000000000000 : ℝ) ≤ (10000655907372859/10000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (50014653894132045873/50000000000000000000 : ℝ)^1024 ≤ (10000655907372859/10000000000000000 : ℝ)^4575 := by
      have hnat : (50014653894132045873 : ℕ)^1024*10000000000000000^4575 ≤ 10000655907372859^4575*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014653894132045873 50000000000000000000 10000655907372859 10000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000655907372859/10000000000000000 : ℝ)) (X := (50014653894132045873/50000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012031041998739289/25000000000000000000 : ℝ) ≤ (10001077000211363/10000000000000000 : ℝ) ^ (4575/1024 : ℝ) := by
    have hpowers : (25012031041998739289/25000000000000000000 : ℝ)^1024 ≤ (10001077000211363/10000000000000000 : ℝ)^4575 := by
      have hnat : (25012031041998739289 : ℕ)^1024*10000000000000000^4575 ≤ 10001077000211363^4575*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012031041998739289 25000000000000000000 10001077000211363 10000000000000000 1024 4575 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001077000211363/10000000000000000 : ℝ)) (X := (25012031041998739289/25000000000000000000 : ℝ)) (by norm_num) 4575 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(327856516663323/6250000000000000000 : ℝ) ≤ ((8948354823961799101/8950000000000000000 : ℝ)+2*(52636604813/55937500000000 : ℝ)*(2203/20000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (8948354823961799101/8950000000000000000 : ℝ)+2*(52636604813/55937500000000 : ℝ)*(2203/20000 : ℝ)=(2000046962906871/2000000000000000 : ℝ) by norm_num, show 1+2*(327856516663323/6250000000000000000 : ℝ)=(3125327856516663323/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12031041998739289/50000000000000000000 : ℝ)+(327856516663323/6250000000000000000 : ℝ) ≤ ((8948354823961799101/8950000000000000000 : ℝ)+(52636604813/55937500000000 : ℝ)*((1549/10000 : ℝ)+(2203/20000 : ℝ)))^(4575/1024 : ℝ) := by
    rw [show (8948354823961799101/8950000000000000000 : ℝ)+(52636604813/55937500000000 : ℝ)*((1549/10000 : ℝ)+(2203/20000 : ℝ))=(10000655907372859/10000000000000000 : ℝ) by norm_num, show 1+(12031041998739289/50000000000000000000 : ℝ)+(327856516663323/6250000000000000000 : ℝ)=(50014653894132045873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12031041998739289/50000000000000000000 : ℝ) ≤ ((8948354823961799101/8950000000000000000 : ℝ)+2*(52636604813/55937500000000 : ℝ)*(1549/10000 : ℝ))^(4575/1024 : ℝ) := by
    rw [show (8948354823961799101/8950000000000000000 : ℝ)+2*(52636604813/55937500000000 : ℝ)*(1549/10000 : ℝ)=(10001077000211363/10000000000000000 : ℝ) by norm_num, show 1+2*(12031041998739289/50000000000000000000 : ℝ)=(25012031041998739289/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8948354823961799101/8950000000000000000 : ℝ)*(X 1 0+X 2 0)+(52636604813/55937500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (8948354823961799101/8950000000000000000 : ℝ)) (alpha := (52636604813/55937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8948354823961799101/8950000000000000000 : ℝ)*(X 0 1+X 2 1)+(52636604813/55937500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (8948354823961799101/8950000000000000000 : ℝ)) (alpha := (52636604813/55937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8948354823961799101/8950000000000000000 : ℝ)*(X 0 2+X 1 2)+(52636604813/55937500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4575/1024 : ℝ)) (lo := (2203/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (8948354823961799101/8950000000000000000 : ℝ)) (alpha := (52636604813/55937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-73097101/400000000 : ℝ)*X 0 0+(5429638429/10000000000 : ℝ)*X 0 1+(1304727127/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349997507/10000000000 : ℝ)*X 1 0+(-1935294309/10000000000 : ℝ)*X 1 1+(1304727127/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674998771/5000000000 : ℝ)*X 2 0+(652363559/1250000000 : ℝ)*X 2 1+(-1935294311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4256906211/10000000000 : ℝ)*X 0 0+(4019045903/10000000000 : ℝ)*X 0 1+(4506336991/10000000000 : ℝ)*X 0 2+(4256906211/10000000000 : ℝ)*X 1 0+(4019045903/10000000000 : ℝ)*X 1 1+(4506336991/10000000000 : ℝ)*X 1 2+(4256906211/10000000000 : ℝ)*X 2 0+(4019045903/10000000000 : ℝ)*X 2 1+(4506336991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-913727697/5000000000 : ℝ)*X 0 0+(5219999637/10000000000 : ℝ)*X 0 1+(21714157/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294456469/10000000000 : ℝ)*X 1 0+(-862831791/5000000000 : ℝ)*X 1 1+(5428539293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294456511/10000000000 : ℝ)*X 2 0+(217141571/400000000 : ℝ)*X 2 1+(-1725663549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((266060669/625000000 : ℝ)*X 0 0+(1125953493/2500000000 : ℝ)*X 0 1+(502698439/1250000000 : ℝ)*X 0 2+(266060669/625000000 : ℝ)*X 1 0+(1125953493/2500000000 : ℝ)*X 1 1+(502698439/1250000000 : ℝ)*X 1 2+(266060669/625000000 : ℝ)*X 2 0+(1125953493/2500000000 : ℝ)*X 2 1+(502698439/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1540_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1019009514582198887554369563/111875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1587479791/100000000000000 : ℝ)*(base19) + (378474067/25000000000000 : ℝ)*(base23) + (1399407/2500000000000 : ℝ)*(lower2) + (55488137/25000000000000 : ℝ)*(upper3) + (29886073/20000000000000 : ℝ)*(upper5) + (849705846045421/25000000000000 : ℝ)*(major0) + (849705846045421/25000000000000 : ℝ)*(major1) + (679764676836337/20000000000000 : ℝ)*(major2) + (4745436909187489/100000000000000 : ℝ)*(sp0) + (4745460939899949/100000000000000 : ℝ)*(sp1) + (296591313342717/6250000000000 : ℝ)*(sp2) + (3283475293319/160000000000 : ℝ)*(sp3) + (25618192251/100000000000000 : ℝ)*(sp4) + (11879043753/100000000000000 : ℝ)*(sp7) + (32065374021377/1562500000000 : ℝ)*(f.failure) + (237273126368987/5000000000000 : ℝ)*(f.sum) + (58700144198881/11187500000000000000000000000 : ℝ)*base66 + (535944277055416521/223750000000000000000000000000000 : ℝ)*base67 + (1373164939323322963/179000000000000000000000000000000 : ℝ)*base70 + (191400333705833479/223750000000000000000000000000000 : ℝ)*base72 + (9838617251/43701171875000000000000000 : ℝ)*base74 + (23704891206677037/179000000000000000000000000000000 : ℝ)*base75 + (211002752772103479/223750000000000000000000000000000 : ℝ)*base78 + (360299104342103479/223750000000000000000000000000000 : ℝ)*base80 + (41748883995639/22375000000000000000000000000 : ℝ)*base82 + (842447/78125000000000000000 : ℝ)*base89 + (842447/78125000000000000000 : ℝ)*base91 + (61197/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83823912377687629224189/11187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (279137083/25000000000000 : ℝ)*(base19) + (1296989613/100000000000000 : ℝ)*(base23) + (89659723/25000000000000 : ℝ)*(lower1) + (172406293/100000000000000 : ℝ)*(upper3) + (14064697/25000000000000 : ℝ)*(lower4) + (137117383/100000000000000 : ℝ)*(upper5) + (3434470282546927/100000000000000 : ℝ)*(major0) + (3434470282546927/100000000000000 : ℝ)*(major1) + (3434470282546927/100000000000000 : ℝ)*(major2) + (344521727/10000000000000 : ℝ)*(sp2) + (959046609892389/20000000000000 : ℝ)*(sp4) + (1198807983228403/25000000000000 : ℝ)*(sp5) + (4795228307255061/100000000000000 : ℝ)*(sp6) + (82948290635089/4000000000000 : ℝ)*(sp7) + (82948290635089/4000000000000 : ℝ)*(f.failure) + (959046609892389/20000000000000 : ℝ)*(f.sum) + (42433476392979/11187500000000000000000000000 : ℝ)*base65 + (11204552030748072627/895000000000000000000000000000000 : ℝ)*base67 + (13349015606826927373/895000000000000000000000000000000 : ℝ)*base70 + (20677705697863072627/895000000000000000000000000000000 : ℝ)*base71 + (10514359264177/5593750000000000000000000000 : ℝ)*base73 + (6996945590896927373/895000000000000000000000000000000 : ℝ)*base76 + (1995818404421927373/895000000000000000000000000000000 : ℝ)*base78 + (3669172696998072627/895000000000000000000000000000000 : ℝ)*base79 + (29288422272333/22375000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (432921/200000000000000000000 : ℝ)*base90 + (432921/200000000000000000000 : ℝ)*base92 + (432921/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1540_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2203/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11019/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1540_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1540_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11019/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1540_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1540_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1540_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4575/1024 : ℝ) ≤ p) (hpb : p ≤ (4577/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82809911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15899/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11019/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1540_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
