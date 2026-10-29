-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1741_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:11.195794+00:00
-- url     : https://prove2.me/submissions/2b9d6e3d-7e4c-4ced-b194-fd8a35785d87

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
theorem support_rectangle_w1741_s3_0 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1274256211/10000000000 : ℝ)*x 0 + (5509464761/10000000000 : ℝ)*x 1 + (5078201233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1274256211/10000000000 : ℝ)^5631 ≤ (8060867252101/100000000000000 : ℝ)^4607 := by
    have hnat : (1274256211 : ℕ)^5631*100000000000000^4607 ≤ 8060867252101^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274256211 10000000000 8060867252101 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509464761/10000000000 : ℝ)^5631 ≤ (2412879779057/5000000000000 : ℝ)^4607 := by
    have hnat : (5509464761 : ℕ)^5631*5000000000000^4607 ≤ 2412879779057^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509464761 10000000000 2412879779057 5000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078201233/10000000000 : ℝ)^5631 ≤ (21840768574429/50000000000000 : ℝ)^4607 := by
    have hnat : (5078201233 : ℕ)^5631*50000000000000^4607 ≤ 21840768574429^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078201233 10000000000 21840768574429 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1274256211/10000000000 : ℝ), (5509464761/10000000000 : ℝ), (5078201233/10000000000 : ℝ)] ![(8060867252101/100000000000000 : ℝ), (2412879779057/5000000000000 : ℝ), (21840768574429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1274256211/10000000000 : ℝ)|^5631 ≤ (8060867252101/100000000000000 : ℝ)^4607
        have hw : |(-1274256211/10000000000 : ℝ)|=(1274256211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509464761/10000000000 : ℝ)|^5631 ≤ (2412879779057/5000000000000 : ℝ)^4607
        have hw : |(5509464761/10000000000 : ℝ)|=(5509464761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078201233/10000000000 : ℝ)|^5631 ≤ (21840768574429/50000000000000 : ℝ)^4607
        have hw : |(5078201233/10000000000 : ℝ)|=(5078201233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s3_1 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335655059/2500000000 : ℝ)*x 0 + (-1500225103/10000000000 : ℝ)*x 1 + (1269550431/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335655059/2500000000 : ℝ)^5631 ≤ (23238716281851/50000000000000 : ℝ)^4607 := by
    have hnat : (1335655059 : ℕ)^5631*50000000000000^4607 ≤ 23238716281851^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335655059 2500000000 23238716281851 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500225103/10000000000 : ℝ)^5631 ≤ (9841025114289/100000000000000 : ℝ)^4607 := by
    have hnat : (1500225103 : ℕ)^5631*100000000000000^4607 ≤ 9841025114289^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500225103 10000000000 9841025114289 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269550431/2500000000 : ℝ)^5631 ≤ (21840771155541/50000000000000 : ℝ)^4607 := by
    have hnat : (1269550431 : ℕ)^5631*50000000000000^4607 ≤ 21840771155541^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269550431 2500000000 21840771155541 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335655059/2500000000 : ℝ), (-1500225103/10000000000 : ℝ), (1269550431/2500000000 : ℝ)] ![(23238716281851/50000000000000 : ℝ), (9841025114289/100000000000000 : ℝ), (21840771155541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335655059/2500000000 : ℝ)|^5631 ≤ (23238716281851/50000000000000 : ℝ)^4607
        have hw : |(1335655059/2500000000 : ℝ)|=(1335655059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1500225103/10000000000 : ℝ)|^5631 ≤ (9841025114289/100000000000000 : ℝ)^4607
        have hw : |(-1500225103/10000000000 : ℝ)|=(1500225103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269550431/2500000000 : ℝ)|^5631 ≤ (21840771155541/50000000000000 : ℝ)^4607
        have hw : |(1269550431/2500000000 : ℝ)|=(1269550431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s3_2 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5342620223/10000000000 : ℝ)*x 0 + (5078201523/10000000000 : ℝ)*x 1 + (-187528173/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342620223/10000000000 : ℝ)^5631 ≤ (46477432425473/100000000000000 : ℝ)^4607 := by
    have hnat : (5342620223 : ℕ)^5631*100000000000000^4607 ≤ 46477432425473^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342620223 10000000000 46477432425473 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078201523/10000000000 : ℝ)^5631 ≤ (4368154019783/10000000000000 : ℝ)^4607 := by
    have hnat : (5078201523 : ℕ)^5631*10000000000000^4607 ≤ 4368154019783^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078201523 10000000000 4368154019783 10000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187528173/1250000000 : ℝ)^5631 ≤ (984102736727/10000000000000 : ℝ)^4607 := by
    have hnat : (187528173 : ℕ)^5631*10000000000000^4607 ≤ 984102736727^4607*1250000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187528173 1250000000 984102736727 10000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342620223/10000000000 : ℝ), (5078201523/10000000000 : ℝ), (-187528173/1250000000 : ℝ)] ![(46477432425473/100000000000000 : ℝ), (4368154019783/10000000000000 : ℝ), (984102736727/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342620223/10000000000 : ℝ)|^5631 ≤ (46477432425473/100000000000000 : ℝ)^4607
        have hw : |(5342620223/10000000000 : ℝ)|=(5342620223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078201523/10000000000 : ℝ)|^5631 ≤ (4368154019783/10000000000000 : ℝ)^4607
        have hw : |(5078201523/10000000000 : ℝ)|=(5078201523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187528173/1250000000 : ℝ)|^5631 ≤ (984102736727/10000000000000 : ℝ)^4607
        have hw : |(-187528173/1250000000 : ℝ)|=(187528173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s3_3 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2020067891/5000000000 : ℝ)*x 0 + (847588589/2500000000 : ℝ)*x 1 + (4755356577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020067891/5000000000 : ℝ)^5631 ≤ (16515031851197/50000000000000 : ℝ)^4607 := by
    have hnat : (2020067891 : ℕ)^5631*50000000000000^4607 ≤ 16515031851197^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020067891 5000000000 16515031851197 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847588589/2500000000 : ℝ)^5631 ≤ (26658300191343/100000000000000 : ℝ)^4607 := by
    have hnat : (847588589 : ℕ)^5631*100000000000000^4607 ≤ 26658300191343^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847588589 2500000000 26658300191343 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4755356577/10000000000 : ℝ)^5631 ≤ (40311636091157/100000000000000 : ℝ)^4607 := by
    have hnat : (4755356577 : ℕ)^5631*100000000000000^4607 ≤ 40311636091157^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4755356577 10000000000 40311636091157 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2020067891/5000000000 : ℝ), (847588589/2500000000 : ℝ), (4755356577/10000000000 : ℝ)] ![(16515031851197/50000000000000 : ℝ), (26658300191343/100000000000000 : ℝ), (40311636091157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2020067891/5000000000 : ℝ)|^5631 ≤ (16515031851197/50000000000000 : ℝ)^4607
        have hw : |(2020067891/5000000000 : ℝ)|=(2020067891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847588589/2500000000 : ℝ)|^5631 ≤ (26658300191343/100000000000000 : ℝ)^4607
        have hw : |(847588589/2500000000 : ℝ)|=(847588589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4755356577/10000000000 : ℝ)|^5631 ≤ (40311636091157/100000000000000 : ℝ)^4607
        have hw : |(4755356577/10000000000 : ℝ)|=(4755356577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s3_4 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1274626731/10000000000 : ℝ)*x 0 + (1271278013/2500000000 : ℝ)*x 1 + (1100481677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1274626731/10000000000 : ℝ)^5631 ≤ (4031866104239/50000000000000 : ℝ)^4607 := by
    have hnat : (1274626731 : ℕ)^5631*50000000000000^4607 ≤ 4031866104239^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274626731 10000000000 4031866104239 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271278013/2500000000 : ℝ)^5631 ≤ (43754206368261/100000000000000 : ℝ)^4607 := by
    have hnat : (1271278013 : ℕ)^5631*100000000000000^4607 ≤ 43754206368261^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271278013 2500000000 43754206368261 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100481677/2000000000 : ℝ)^5631 ≤ (48182061411869/100000000000000 : ℝ)^4607 := by
    have hnat : (1100481677 : ℕ)^5631*100000000000000^4607 ≤ 48182061411869^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100481677 2000000000 48182061411869 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1274626731/10000000000 : ℝ), (1271278013/2500000000 : ℝ), (1100481677/2000000000 : ℝ)] ![(4031866104239/50000000000000 : ℝ), (43754206368261/100000000000000 : ℝ), (48182061411869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1274626731/10000000000 : ℝ)|^5631 ≤ (4031866104239/50000000000000 : ℝ)^4607
        have hw : |(-1274626731/10000000000 : ℝ)|=(1274626731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271278013/2500000000 : ℝ)|^5631 ≤ (43754206368261/100000000000000 : ℝ)^4607
        have hw : |(1271278013/2500000000 : ℝ)|=(1271278013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100481677/2000000000 : ℝ)|^5631 ≤ (48182061411869/100000000000000 : ℝ)^4607
        have hw : |(1100481677/2000000000 : ℝ)|=(1100481677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s3_5 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653507083/1250000000 : ℝ)*x 0 + (-1076018681/10000000000 : ℝ)*x 1 + (2751203993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653507083/1250000000 : ℝ)^5631 ≤ (45262199277963/100000000000000 : ℝ)^4607 := by
    have hnat : (653507083 : ℕ)^5631*100000000000000^4607 ≤ 45262199277963^4607*1250000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653507083 1250000000 45262199277963 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076018681/10000000000 : ℝ)^5631 ≤ (1311148712923/20000000000000 : ℝ)^4607 := by
    have hnat : (1076018681 : ℕ)^5631*20000000000000^4607 ≤ 1311148712923^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076018681 10000000000 1311148712923 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751203993/5000000000 : ℝ)^5631 ≤ (12045514285357/25000000000000 : ℝ)^4607 := by
    have hnat : (2751203993 : ℕ)^5631*25000000000000^4607 ≤ 12045514285357^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751203993 5000000000 12045514285357 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653507083/1250000000 : ℝ), (-1076018681/10000000000 : ℝ), (2751203993/5000000000 : ℝ)] ![(45262199277963/100000000000000 : ℝ), (1311148712923/20000000000000 : ℝ), (12045514285357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653507083/1250000000 : ℝ)|^5631 ≤ (45262199277963/100000000000000 : ℝ)^4607
        have hw : |(653507083/1250000000 : ℝ)|=(653507083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076018681/10000000000 : ℝ)|^5631 ≤ (1311148712923/20000000000000 : ℝ)^4607
        have hw : |(-1076018681/10000000000 : ℝ)|=(1076018681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751203993/5000000000 : ℝ)|^5631 ≤ (12045514285357/25000000000000 : ℝ)^4607
        have hw : |(2751203993/5000000000 : ℝ)|=(2751203993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s3_6 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653507099/1250000000 : ℝ)*x 0 + (5502407539/10000000000 : ℝ)*x 1 + (-1076019141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653507099/1250000000 : ℝ)^5631 ≤ (45262200632443/100000000000000 : ℝ)^4607 := by
    have hnat : (653507099 : ℕ)^5631*100000000000000^4607 ≤ 45262200632443^4607*1250000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653507099 1250000000 45262200632443 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502407539/10000000000 : ℝ)^5631 ≤ (48182052357249/100000000000000 : ℝ)^4607 := by
    have hnat : (5502407539 : ℕ)^5631*100000000000000^4607 ≤ 48182052357249^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502407539 10000000000 48182052357249 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076019141/10000000000 : ℝ)^5631 ≤ (6555746990141/100000000000000 : ℝ)^4607 := by
    have hnat : (1076019141 : ℕ)^5631*100000000000000^4607 ≤ 6555746990141^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076019141 10000000000 6555746990141 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653507099/1250000000 : ℝ), (5502407539/10000000000 : ℝ), (-1076019141/10000000000 : ℝ)] ![(45262200632443/100000000000000 : ℝ), (48182052357249/100000000000000 : ℝ), (6555746990141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653507099/1250000000 : ℝ)|^5631 ≤ (45262200632443/100000000000000 : ℝ)^4607
        have hw : |(653507099/1250000000 : ℝ)|=(653507099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502407539/10000000000 : ℝ)|^5631 ≤ (48182052357249/100000000000000 : ℝ)^4607
        have hw : |(5502407539/10000000000 : ℝ)|=(5502407539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076019141/10000000000 : ℝ)|^5631 ≤ (6555746990141/100000000000000 : ℝ)^4607
        have hw : |(-1076019141/10000000000 : ℝ)|=(1076019141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_s3_7 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4041308707/10000000000 : ℝ)*x 0 + (236674081/500000000 : ℝ)*x 1 + (3412689821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4041308707/10000000000 : ℝ)^5631 ≤ (33041784711929/100000000000000 : ℝ)^4607 := by
    have hnat : (4041308707 : ℕ)^5631*100000000000000^4607 ≤ 33041784711929^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041308707 10000000000 33041784711929 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236674081/500000000 : ℝ)^5631 ≤ (20042549449369/50000000000000 : ℝ)^4607 := by
    have hnat : (236674081 : ℕ)^5631*50000000000000^4607 ≤ 20042549449369^4607*500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236674081 500000000 20042549449369 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3412689821/10000000000 : ℝ)^5631 ≤ (26873116370421/100000000000000 : ℝ)^4607 := by
    have hnat : (3412689821 : ℕ)^5631*100000000000000^4607 ≤ 26873116370421^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3412689821 10000000000 26873116370421 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4041308707/10000000000 : ℝ), (236674081/500000000 : ℝ), (3412689821/10000000000 : ℝ)] ![(33041784711929/100000000000000 : ℝ), (20042549449369/50000000000000 : ℝ), (26873116370421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4041308707/10000000000 : ℝ)|^5631 ≤ (33041784711929/100000000000000 : ℝ)^4607
        have hw : |(4041308707/10000000000 : ℝ)|=(4041308707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(236674081/500000000 : ℝ)|^5631 ≤ (20042549449369/50000000000000 : ℝ)^4607
        have hw : |(236674081/500000000 : ℝ)|=(236674081/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3412689821/10000000000 : ℝ)|^5631 ≤ (26873116370421/100000000000000 : ℝ)^4607
        have hw : |(3412689821/10000000000 : ℝ)|=(3412689821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1741_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9077/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1783/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2269/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9077/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9077/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9077/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9077/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9077/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9077/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8913/100000 : ℝ) ^ (5615/1024 : ℝ) ≤ (174808573818181/100000000000000000000 : ℝ) := by
    have hpowers : (8913/100000 : ℝ)^5615 ≤ (174808573818181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8913 : ℕ)^5615*100000000000000000000^1024 ≤ 174808573818181^1024*100000^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8913 100000 174808573818181 100000000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8913/100000 : ℝ)) (X := (174808573818181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9077/50000 : ℝ) ^ (5615/1024 : ℝ) ≤ (8642711939500131/100000000000000000000 : ℝ) := by
    have hpowers : (9077/50000 : ℝ)^5615 ≤ (8642711939500131/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9077 : ℕ)^5615*100000000000000000000^1024 ≤ 8642711939500131^1024*50000^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9077 50000 8642711939500131 100000000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9077/50000 : ℝ)) (X := (8642711939500131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000174808573818181/50000000000000000000 : ℝ) ≤ (10000006375911799/10000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (50000174808573818181/50000000000000000000 : ℝ)^1024 ≤ (10000006375911799/10000000000000000 : ℝ)^5615 := by
      have hnat : (50000174808573818181 : ℕ)^1024*10000000000000000^5615 ≤ 10000006375911799^5615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000174808573818181 50000000000000000000 10000006375911799 10000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000006375911799/10000000000000000 : ℝ)) (X := (50000174808573818181/50000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501102190064164789/12500000000000000000 : ℝ) ≤ (2500040199534933/2500000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (12501102190064164789/12500000000000000000 : ℝ)^1024 ≤ (2500040199534933/2500000000000000 : ℝ)^5615 := by
      have hnat : (12501102190064164789 : ℕ)^1024*2500000000000000^5615 ≤ 2500040199534933^5615*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501102190064164789 12500000000000000000 2500040199534933 2500000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500040199534933/2500000000000000 : ℝ)) (X := (12501102190064164789/12500000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008642711939500131/50000000000000000000 : ℝ) ≤ (2000063044073533/2000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (50008642711939500131/50000000000000000000 : ℝ)^1024 ≤ (2000063044073533/2000000000000000 : ℝ)^5615 := by
      have hnat : (50008642711939500131 : ℕ)^1024*2000000000000000^5615 ≤ 2000063044073533^5615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008642711939500131 50000000000000000000 2000063044073533 2000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000063044073533/2000000000000000 : ℝ)) (X := (50008642711939500131/50000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(174808573818181/100000000000000000000 : ℝ) ≤ ((92407306189165800901/92410000000000000000 : ℝ)+2*(154422227933/924100000000000 : ℝ)*(8913/100000 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (92407306189165800901/92410000000000000000 : ℝ)+2*(154422227933/924100000000000 : ℝ)*(8913/100000 : ℝ)=(10000006375911799/10000000000000000 : ℝ) by norm_num, show 1+2*(174808573818181/100000000000000000000 : ℝ)=(50000174808573818181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8642711939500131/100000000000000000000 : ℝ)+(174808573818181/100000000000000000000 : ℝ) ≤ ((92407306189165800901/92410000000000000000 : ℝ)+(154422227933/924100000000000 : ℝ)*((9077/50000 : ℝ)+(8913/100000 : ℝ)))^(5615/1024 : ℝ) := by
    rw [show (92407306189165800901/92410000000000000000 : ℝ)+(154422227933/924100000000000 : ℝ)*((9077/50000 : ℝ)+(8913/100000 : ℝ))=(2500040199534933/2500000000000000 : ℝ) by norm_num, show 1+(8642711939500131/100000000000000000000 : ℝ)+(174808573818181/100000000000000000000 : ℝ)=(12501102190064164789/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8642711939500131/100000000000000000000 : ℝ) ≤ ((92407306189165800901/92410000000000000000 : ℝ)+2*(154422227933/924100000000000 : ℝ)*(9077/50000 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (92407306189165800901/92410000000000000000 : ℝ)+2*(154422227933/924100000000000 : ℝ)*(9077/50000 : ℝ)=(2000063044073533/2000000000000000 : ℝ) by norm_num, show 1+2*(8642711939500131/100000000000000000000 : ℝ)=(50008642711939500131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92407306189165800901/92410000000000000000 : ℝ)*(X 1 0+X 2 0)+(154422227933/924100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (8913/100000 : ℝ)) (hi := (9077/50000 : ℝ)) (c := (92407306189165800901/92410000000000000000 : ℝ)) (alpha := (154422227933/924100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92407306189165800901/92410000000000000000 : ℝ)*(X 0 1+X 2 1)+(154422227933/924100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (8913/100000 : ℝ)) (hi := (9077/50000 : ℝ)) (c := (92407306189165800901/92410000000000000000 : ℝ)) (alpha := (154422227933/924100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92407306189165800901/92410000000000000000 : ℝ)*(X 0 2+X 1 2)+(154422227933/924100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (8913/100000 : ℝ)) (hi := (9077/50000 : ℝ)) (c := (92407306189165800901/92410000000000000000 : ℝ)) (alpha := (154422227933/924100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1274256211/10000000000 : ℝ)*X 0 0+(5509464761/10000000000 : ℝ)*X 0 1+(5078201233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1335655059/2500000000 : ℝ)*X 1 0+(-1500225103/10000000000 : ℝ)*X 1 1+(1269550431/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5342620223/10000000000 : ℝ)*X 2 0+(5078201523/10000000000 : ℝ)*X 2 1+(-187528173/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2020067891/5000000000 : ℝ)*X 0 0+(847588589/2500000000 : ℝ)*X 0 1+(4755356577/10000000000 : ℝ)*X 0 2+(2020067891/5000000000 : ℝ)*X 1 0+(847588589/2500000000 : ℝ)*X 1 1+(4755356577/10000000000 : ℝ)*X 1 2+(2020067891/5000000000 : ℝ)*X 2 0+(847588589/2500000000 : ℝ)*X 2 1+(4755356577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1274626731/10000000000 : ℝ)*X 0 0+(1271278013/2500000000 : ℝ)*X 0 1+(1100481677/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((653507083/1250000000 : ℝ)*X 1 0+(-1076018681/10000000000 : ℝ)*X 1 1+(2751203993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((653507099/1250000000 : ℝ)*X 2 0+(5502407539/10000000000 : ℝ)*X 2 1+(-1076019141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4041308707/10000000000 : ℝ)*X 0 0+(236674081/500000000 : ℝ)*X 0 1+(3412689821/10000000000 : ℝ)*X 0 2+(4041308707/10000000000 : ℝ)*X 1 0+(236674081/500000000 : ℝ)*X 1 1+(3412689821/10000000000 : ℝ)*X 1 2+(4041308707/10000000000 : ℝ)*X 2 0+(236674081/500000000 : ℝ)*X 2 1+(3412689821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (315312626125605377650893/46205000000000000000000000000 : ℝ) := by norm_num
    linear_combination (962854119/100000000000000 : ℝ)*(base19) + (474705469/50000000000000 : ℝ)*(base23) + (248382723/100000000000000 : ℝ)*(upper3) + (4167761/100000000000000 : ℝ)*(upper4) + (51101623/50000000000000 : ℝ)*(upper5) + (1525695786669423/100000000000000 : ℝ)*(major0) + (1525695786669423/100000000000000 : ℝ)*(major1) + (1525695786669423/100000000000000 : ℝ)*(major2) + (463755547600093/20000000000000 : ℝ)*(sp0) + (2318784775177217/100000000000000 : ℝ)*(sp1) + (1159392394310199/50000000000000 : ℝ)*(sp2) + (73260223011439/10000000000000 : ℝ)*(sp3) + (8000030871/100000000000000 : ℝ)*(sp4) + (675543889/20000000000000 : ℝ)*(sp7) + (183151401958459/25000000000000 : ℝ)*(f.failure) + (289848217253917/12500000000000 : ℝ)*(f.sum) + (1143804624009/11551250000000000000000000000 : ℝ)*base66 + (25906662197211450123/9241000000000000000000000000000000 : ℝ)*base67 + (39443025393133450123/9241000000000000000000000000000000 : ℝ)*base69 + (22943286750098549877/9241000000000000000000000000000000 : ℝ)*base72 + (64780204796957/23102500000000000000000000000 : ℝ)*base73 + (52305615542985450123/9241000000000000000000000000000000 : ℝ)*base75 + (9957330303720549877/9241000000000000000000000000000000 : ℝ)*base78 + (40436278770065549877/9241000000000000000000000000000000 : ℝ)*base80 + (16469253882293/5775625000000000000000000000 : ℝ)*base81 + (36806851/2500000000000000000000 : ℝ)*base89 + (36806851/2500000000000000000000 : ℝ)*base91 + (36806851/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51941968483472362673473181691/4620500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26660259/1562500000000 : ℝ)*(base19) + (435509473/25000000000000 : ℝ)*(base23) + (15165497/5000000000000 : ℝ)*(lower1) + (222957187/100000000000000 : ℝ)*(upper3) + (6833421/25000000000000 : ℝ)*(lower4) + (167193269/50000000000000 : ℝ)*(upper5) + (1576745910656597/100000000000000 : ℝ)*(major0) + (1576745910656597/100000000000000 : ℝ)*(major1) + (1576745910656597/100000000000000 : ℝ)*(major2) + (1715229247/50000000000000 : ℝ)*(sp1) + (1198186345217873/50000000000000 : ℝ)*(sp4) + (599091888430169/25000000000000 : ℝ)*(sp5) + (2396370948397853/100000000000000 : ℝ)*(sp6) + (757118756156319/100000000000000 : ℝ)*(sp7) + (757118756156319/100000000000000 : ℝ)*(f.failure) + (1198186345217873/50000000000000 : ℝ)*(f.sum) + (53715451627717/23102500000000000000000000000 : ℝ)*base66 + (81474345958167706103/9241000000000000000000000000000000 : ℝ)*base68 + (15165472251584706103/9241000000000000000000000000000000 : ℝ)*base70 + (87378156648736706103/9241000000000000000000000000000000 : ℝ)*base72 + (105804040684109/46205000000000000000000000000 : ℝ)*base74 + (32564722597246706103/9241000000000000000000000000000000 : ℝ)*base76 + (5623284650415293897/9241000000000000000000000000000000 : ℝ)*base77 + (18306248149857293897/9241000000000000000000000000000000 : ℝ)*base79 + (82629602279671/46205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (32423609/10000000000000000000000 : ℝ)*base90 + (32423609/10000000000000000000000 : ℝ)*base92 + (32423609/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1741_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9077/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1783/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2269/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1741_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1741_box_0 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-436031343/5000000000 : ℝ)*x 0 + (2717644989/5000000000 : ℝ)*x 1 + (1358822529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436031343/5000000000 : ℝ)^5631 ≤ (5070639756379/100000000000000 : ℝ)^4607 := by
    have hnat : (436031343 : ℕ)^5631*100000000000000^4607 ≤ 5070639756379^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436031343 5000000000 5070639756379 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717644989/5000000000 : ℝ)^5631 ≤ (23732339688779/50000000000000 : ℝ)^4607 := by
    have hnat : (2717644989 : ℕ)^5631*50000000000000^4607 ≤ 23732339688779^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717644989 5000000000 23732339688779 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358822529/2500000000 : ℝ)^5631 ≤ (47464680850529/100000000000000 : ℝ)^4607 := by
    have hnat : (1358822529 : ℕ)^5631*100000000000000^4607 ≤ 47464680850529^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358822529 2500000000 47464680850529 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436031343/5000000000 : ℝ), (2717644989/5000000000 : ℝ), (1358822529/2500000000 : ℝ)] ![(5070639756379/100000000000000 : ℝ), (23732339688779/50000000000000 : ℝ), (47464680850529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436031343/5000000000 : ℝ)|^5631 ≤ (5070639756379/100000000000000 : ℝ)^4607
        have hw : |(-436031343/5000000000 : ℝ)|=(436031343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717644989/5000000000 : ℝ)|^5631 ≤ (23732339688779/50000000000000 : ℝ)^4607
        have hw : |(2717644989/5000000000 : ℝ)|=(2717644989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358822529/2500000000 : ℝ)|^5631 ≤ (47464680850529/100000000000000 : ℝ)^4607
        have hw : |(1358822529/2500000000 : ℝ)|=(1358822529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_1 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195113703/10000000000 : ℝ)*x 0 + (-1217140447/10000000000 : ℝ)*x 1 + (5435290119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195113703/10000000000 : ℝ)^5631 ≤ (22456922728269/50000000000000 : ℝ)^4607 := by
    have hnat : (5195113703 : ℕ)^5631*50000000000000^4607 ≤ 22456922728269^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195113703 10000000000 22456922728269 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1217140447/10000000000 : ℝ)^5631 ≤ (95268420543/1250000000000 : ℝ)^4607 := by
    have hnat : (1217140447 : ℕ)^5631*1250000000000^4607 ≤ 95268420543^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217140447 10000000000 95268420543 1250000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435290119/10000000000 : ℝ)^5631 ≤ (949293617651/2000000000000 : ℝ)^4607 := by
    have hnat : (5435290119 : ℕ)^5631*2000000000000^4607 ≤ 949293617651^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435290119 10000000000 949293617651 2000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195113703/10000000000 : ℝ), (-1217140447/10000000000 : ℝ), (5435290119/10000000000 : ℝ)] ![(22456922728269/50000000000000 : ℝ), (95268420543/1250000000000 : ℝ), (949293617651/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195113703/10000000000 : ℝ)|^5631 ≤ (22456922728269/50000000000000 : ℝ)^4607
        have hw : |(5195113703/10000000000 : ℝ)|=(5195113703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1217140447/10000000000 : ℝ)|^5631 ≤ (95268420543/1250000000000 : ℝ)^4607
        have hw : |(-1217140447/10000000000 : ℝ)|=(1217140447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435290119/10000000000 : ℝ)|^5631 ≤ (949293617651/2000000000000 : ℝ)^4607
        have hw : |(5435290119/10000000000 : ℝ)|=(5435290119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_2 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298778289/2500000000 : ℝ)*x 0 + (5435290507/10000000000 : ℝ)*x 1 + (-1217140661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298778289/2500000000 : ℝ)^5631 ≤ (44913839676379/100000000000000 : ℝ)^4607 := by
    have hnat : (1298778289 : ℕ)^5631*100000000000000^4607 ≤ 44913839676379^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298778289 2500000000 44913839676379 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435290507/10000000000 : ℝ)^5631 ≤ (47464685023947/100000000000000 : ℝ)^4607 := by
    have hnat : (5435290507 : ℕ)^5631*100000000000000^4607 ≤ 47464685023947^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435290507 10000000000 47464685023947 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217140661/10000000000 : ℝ)^5631 ≤ (7621475281309/100000000000000 : ℝ)^4607 := by
    have hnat : (1217140661 : ℕ)^5631*100000000000000^4607 ≤ 7621475281309^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217140661 10000000000 7621475281309 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298778289/2500000000 : ℝ), (5435290507/10000000000 : ℝ), (-1217140661/10000000000 : ℝ)] ![(44913839676379/100000000000000 : ℝ), (47464685023947/100000000000000 : ℝ), (7621475281309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298778289/2500000000 : ℝ)|^5631 ≤ (44913839676379/100000000000000 : ℝ)^4607
        have hw : |(1298778289/2500000000 : ℝ)|=(1298778289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435290507/10000000000 : ℝ)|^5631 ≤ (47464685023947/100000000000000 : ℝ)^4607
        have hw : |(5435290507/10000000000 : ℝ)|=(5435290507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217140661/10000000000 : ℝ)|^5631 ≤ (7621475281309/100000000000000 : ℝ)^4607
        have hw : |(-1217140661/10000000000 : ℝ)|=(1217140661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_3 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (228411649/500000000 : ℝ)*x 0 + (763300379/2000000000 : ℝ)*x 1 + (763300531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228411649/500000000 : ℝ)^5631 ≤ (4685224307/12207031250 : ℝ)^4607 := by
    have hnat : (228411649 : ℕ)^5631*12207031250^4607 ≤ 4685224307^4607*500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228411649 500000000 4685224307 12207031250 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (763300379/2000000000 : ℝ)^5631 ≤ (7702329370759/25000000000000 : ℝ)^4607 := by
    have hnat : (763300379 : ℕ)^5631*25000000000000^4607 ≤ 7702329370759^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763300379 2000000000 7702329370759 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (763300531/2000000000 : ℝ)^5631 ≤ (6161864996387/20000000000000 : ℝ)^4607 := by
    have hnat : (763300531 : ℕ)^5631*20000000000000^4607 ≤ 6161864996387^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763300531 2000000000 6161864996387 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(228411649/500000000 : ℝ), (763300379/2000000000 : ℝ), (763300531/2000000000 : ℝ)] ![(4685224307/12207031250 : ℝ), (7702329370759/25000000000000 : ℝ), (6161864996387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(228411649/500000000 : ℝ)|^5631 ≤ (4685224307/12207031250 : ℝ)^4607
        have hw : |(228411649/500000000 : ℝ)|=(228411649/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(763300379/2000000000 : ℝ)|^5631 ≤ (7702329370759/25000000000000 : ℝ)^4607
        have hw : |(763300379/2000000000 : ℝ)|=(763300379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(763300531/2000000000 : ℝ)|^5631 ≤ (6161864996387/20000000000000 : ℝ)^4607
        have hw : |(763300531/2000000000 : ℝ)|=(763300531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_4 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-429206359/2500000000 : ℝ)*x 0 + (5127245217/10000000000 : ℝ)*x 1 + (1025449101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429206359/2500000000 : ℝ)^5631 ≤ (116045516939/1000000000000 : ℝ)^4607 := by
    have hnat : (429206359 : ℕ)^5631*1000000000000^4607 ≤ 116045516939^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429206359 2500000000 116045516939 1000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127245217/10000000000 : ℝ)^5631 ≤ (22098861316671/50000000000000 : ℝ)^4607 := by
    have hnat : (5127245217 : ℕ)^5631*50000000000000^4607 ≤ 22098861316671^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127245217 10000000000 22098861316671 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025449101/2000000000 : ℝ)^5631 ≤ (22098862833881/50000000000000 : ℝ)^4607 := by
    have hnat : (1025449101 : ℕ)^5631*50000000000000^4607 ≤ 22098862833881^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025449101 2000000000 22098862833881 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429206359/2500000000 : ℝ), (5127245217/10000000000 : ℝ), (1025449101/2000000000 : ℝ)] ![(116045516939/1000000000000 : ℝ), (22098861316671/50000000000000 : ℝ), (22098862833881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429206359/2500000000 : ℝ)|^5631 ≤ (116045516939/1000000000000 : ℝ)^4607
        have hw : |(-429206359/2500000000 : ℝ)|=(429206359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127245217/10000000000 : ℝ)|^5631 ≤ (22098861316671/50000000000000 : ℝ)^4607
        have hw : |(5127245217/10000000000 : ℝ)|=(5127245217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025449101/2000000000 : ℝ)|^5631 ≤ (22098862833881/50000000000000 : ℝ)^4607
        have hw : |(1025449101/2000000000 : ℝ)|=(1025449101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_5 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5402125667/10000000000 : ℝ)*x 0 + (-1355234289/10000000000 : ℝ)*x 1 + (5127245403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402125667/10000000000 : ℝ)^5631 ≤ (2944433360417/6250000000000 : ℝ)^4607 := by
    have hnat : (5402125667 : ℕ)^5631*6250000000000^4607 ≤ 2944433360417^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402125667 10000000000 2944433360417 6250000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355234289/10000000000 : ℝ)^5631 ≤ (135802212727/1562500000000 : ℝ)^4607 := by
    have hnat : (1355234289 : ℕ)^5631*1562500000000^4607 ≤ 135802212727^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355234289 10000000000 135802212727 1562500000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127245403/10000000000 : ℝ)^5631 ≤ (2762357787067/6250000000000 : ℝ)^4607 := by
    have hnat : (5127245403 : ℕ)^5631*6250000000000^4607 ≤ 2762357787067^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127245403 10000000000 2762357787067 6250000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402125667/10000000000 : ℝ), (-1355234289/10000000000 : ℝ), (5127245403/10000000000 : ℝ)] ![(2944433360417/6250000000000 : ℝ), (135802212727/1562500000000 : ℝ), (2762357787067/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402125667/10000000000 : ℝ)|^5631 ≤ (2944433360417/6250000000000 : ℝ)^4607
        have hw : |(5402125667/10000000000 : ℝ)|=(5402125667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1355234289/10000000000 : ℝ)|^5631 ≤ (135802212727/1562500000000 : ℝ)^4607
        have hw : |(-1355234289/10000000000 : ℝ)|=(1355234289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127245403/10000000000 : ℝ)|^5631 ≤ (2762357787067/6250000000000 : ℝ)^4607
        have hw : |(5127245403/10000000000 : ℝ)|=(5127245403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_6 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701062727/5000000000 : ℝ)*x 0 + (1025449133/2000000000 : ℝ)*x 1 + (-1355234227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701062727/5000000000 : ℝ)^5631 ≤ (47110931496263/100000000000000 : ℝ)^4607 := by
    have hnat : (2701062727 : ℕ)^5631*100000000000000^4607 ≤ 47110931496263^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701062727 5000000000 47110931496263 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025449133/2000000000 : ℝ)^5631 ≤ (883954547071/2000000000000 : ℝ)^4607 := by
    have hnat : (1025449133 : ℕ)^5631*2000000000000^4607 ≤ 883954547071^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025449133 2000000000 883954547071 2000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355234227/10000000000 : ℝ)^5631 ≤ (4345670564267/50000000000000 : ℝ)^4607 := by
    have hnat : (1355234227 : ℕ)^5631*50000000000000^4607 ≤ 4345670564267^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355234227 10000000000 4345670564267 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701062727/5000000000 : ℝ), (1025449133/2000000000 : ℝ), (-1355234227/10000000000 : ℝ)] ![(47110931496263/100000000000000 : ℝ), (883954547071/2000000000000 : ℝ), (4345670564267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701062727/5000000000 : ℝ)|^5631 ≤ (47110931496263/100000000000000 : ℝ)^4607
        have hw : |(2701062727/5000000000 : ℝ)|=(2701062727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1025449133/2000000000 : ℝ)|^5631 ≤ (883954547071/2000000000000 : ℝ)^4607
        have hw : |(1025449133/2000000000 : ℝ)|=(1025449133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1355234227/10000000000 : ℝ)|^5631 ≤ (4345670564267/50000000000000 : ℝ)^4607
        have hw : |(-1355234227/10000000000 : ℝ)|=(1355234227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_7 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3477022861/10000000000 : ℝ)*x 0 + (217996461/500000000 : ℝ)*x 1 + (2179964657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3477022861/10000000000 : ℝ)^5631 ≤ (687339885067/2500000000000 : ℝ)^4607 := by
    have hnat : (3477022861 : ℕ)^5631*2500000000000^4607 ≤ 687339885067^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3477022861 10000000000 687339885067 2500000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217996461/500000000 : ℝ)^5631 ≤ (9063300453483/25000000000000 : ℝ)^4607 := by
    have hnat : (217996461 : ℕ)^5631*25000000000000^4607 ≤ 9063300453483^4607*500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217996461 500000000 9063300453483 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179964657/5000000000 : ℝ)^5631 ≤ (36253202769281/100000000000000 : ℝ)^4607 := by
    have hnat : (2179964657 : ℕ)^5631*100000000000000^4607 ≤ 36253202769281^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179964657 5000000000 36253202769281 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3477022861/10000000000 : ℝ), (217996461/500000000 : ℝ), (2179964657/5000000000 : ℝ)] ![(687339885067/2500000000000 : ℝ), (9063300453483/25000000000000 : ℝ), (36253202769281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3477022861/10000000000 : ℝ)|^5631 ≤ (687339885067/2500000000000 : ℝ)^4607
        have hw : |(3477022861/10000000000 : ℝ)|=(3477022861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217996461/500000000 : ℝ)|^5631 ≤ (9063300453483/25000000000000 : ℝ)^4607
        have hw : |(217996461/500000000 : ℝ)|=(217996461/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2179964657/5000000000 : ℝ)|^5631 ≤ (36253202769281/100000000000000 : ℝ)^4607
        have hw : |(2179964657/5000000000 : ℝ)|=(2179964657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_8 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1533407181/10000000000 : ℝ)*x 0 + (2446839383/5000000000 : ℝ)*x 1 + (5498744113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1533407181/10000000000 : ℝ)^5631 ≤ (1263465023047/12500000000000 : ℝ)^4607 := by
    have hnat : (1533407181 : ℕ)^5631*12500000000000^4607 ≤ 1263465023047^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533407181 10000000000 1263465023047 12500000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2446839383/5000000000 : ℝ)^5631 ≤ (41749433678471/100000000000000 : ℝ)^4607 := by
    have hnat : (2446839383 : ℕ)^5631*100000000000000^4607 ≤ 41749433678471^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446839383 5000000000 41749433678471 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498744113/10000000000 : ℝ)^5631 ≤ (12035711530557/25000000000000 : ℝ)^4607 := by
    have hnat : (5498744113 : ℕ)^5631*25000000000000^4607 ≤ 12035711530557^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498744113 10000000000 12035711530557 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1533407181/10000000000 : ℝ), (2446839383/5000000000 : ℝ), (5498744113/10000000000 : ℝ)] ![(1263465023047/12500000000000 : ℝ), (41749433678471/100000000000000 : ℝ), (12035711530557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1533407181/10000000000 : ℝ)|^5631 ≤ (1263465023047/12500000000000 : ℝ)^4607
        have hw : |(-1533407181/10000000000 : ℝ)|=(1533407181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2446839383/5000000000 : ℝ)|^5631 ≤ (41749433678471/100000000000000 : ℝ)^4607
        have hw : |(2446839383/5000000000 : ℝ)|=(2446839383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498744113/10000000000 : ℝ)|^5631 ≤ (12035711530557/25000000000000 : ℝ)^4607
        have hw : |(5498744113/10000000000 : ℝ)|=(5498744113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_9 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576264311/5000000000 : ℝ)*x 0 + (-1187191177/10000000000 : ℝ)*x 1 + (1099749011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576264311/5000000000 : ℝ)^5631 ≤ (22232129452111/50000000000000 : ℝ)^4607 := by
    have hnat : (2576264311 : ℕ)^5631*50000000000000^4607 ≤ 22232129452111^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576264311 5000000000 22232129452111 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1187191177/10000000000 : ℝ)^5631 ≤ (1848221220501/25000000000000 : ℝ)^4607 := by
    have hnat : (1187191177 : ℕ)^5631*25000000000000^4607 ≤ 1848221220501^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187191177 10000000000 1848221220501 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099749011/2000000000 : ℝ)^5631 ≤ (4814285620283/10000000000000 : ℝ)^4607 := by
    have hnat : (1099749011 : ℕ)^5631*10000000000000^4607 ≤ 4814285620283^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099749011 2000000000 4814285620283 10000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576264311/5000000000 : ℝ), (-1187191177/10000000000 : ℝ), (1099749011/2000000000 : ℝ)] ![(22232129452111/50000000000000 : ℝ), (1848221220501/25000000000000 : ℝ), (4814285620283/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576264311/5000000000 : ℝ)|^5631 ≤ (22232129452111/50000000000000 : ℝ)^4607
        have hw : |(2576264311/5000000000 : ℝ)|=(2576264311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1187191177/10000000000 : ℝ)|^5631 ≤ (1848221220501/25000000000000 : ℝ)^4607
        have hw : |(-1187191177/10000000000 : ℝ)|=(1187191177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099749011/2000000000 : ℝ)|^5631 ≤ (4814285620283/10000000000000 : ℝ)^4607
        have hw : |(1099749011/2000000000 : ℝ)|=(1099749011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_10 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1288132129/2500000000 : ℝ)*x 0 + (5498744963/10000000000 : ℝ)*x 1 + (-1187191453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1288132129/2500000000 : ℝ)^5631 ≤ (8892851557233/20000000000000 : ℝ)^4607 := by
    have hnat : (1288132129 : ℕ)^5631*20000000000000^4607 ≤ 8892851557233^4607*2500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288132129 2500000000 8892851557233 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498744963/10000000000 : ℝ)^5631 ≤ (6017856902289/12500000000000 : ℝ)^4607 := by
    have hnat : (5498744963 : ℕ)^5631*12500000000000^4607 ≤ 6017856902289^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498744963 10000000000 6017856902289 12500000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187191453/10000000000 : ℝ)^5631 ≤ (1848221745683/25000000000000 : ℝ)^4607 := by
    have hnat : (1187191453 : ℕ)^5631*25000000000000^4607 ≤ 1848221745683^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187191453 10000000000 1848221745683 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1288132129/2500000000 : ℝ), (5498744963/10000000000 : ℝ), (-1187191453/10000000000 : ℝ)] ![(8892851557233/20000000000000 : ℝ), (6017856902289/12500000000000 : ℝ), (1848221745683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1288132129/2500000000 : ℝ)|^5631 ≤ (8892851557233/20000000000000 : ℝ)^4607
        have hw : |(1288132129/2500000000 : ℝ)|=(1288132129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498744963/10000000000 : ℝ)|^5631 ≤ (6017856902289/12500000000000 : ℝ)^4607
        have hw : |(5498744963/10000000000 : ℝ)|=(5498744963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1187191453/10000000000 : ℝ)|^5631 ≤ (1848221745683/25000000000000 : ℝ)^4607
        have hw : |(-1187191453/10000000000 : ℝ)|=(1187191453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_11 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4782336689/10000000000 : ℝ)*x 0 + (1852070967/5000000000 : ℝ)*x 1 + (370414173/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4782336689/10000000000 : ℝ)^5631 ≤ (40591361393819/100000000000000 : ℝ)^4607 := by
    have hnat : (4782336689 : ℕ)^5631*100000000000000^4607 ≤ 40591361393819^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782336689 10000000000 40591361393819 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1852070967/5000000000 : ℝ)^5631 ≤ (29704320292767/100000000000000 : ℝ)^4607 := by
    have hnat : (1852070967 : ℕ)^5631*100000000000000^4607 ≤ 29704320292767^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852070967 5000000000 29704320292767 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370414173/1000000000 : ℝ)^5631 ≤ (29704318293229/100000000000000 : ℝ)^4607 := by
    have hnat : (370414173 : ℕ)^5631*100000000000000^4607 ≤ 29704318293229^4607*1000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370414173 1000000000 29704318293229 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4782336689/10000000000 : ℝ), (1852070967/5000000000 : ℝ), (370414173/1000000000 : ℝ)] ![(40591361393819/100000000000000 : ℝ), (29704320292767/100000000000000 : ℝ), (29704318293229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4782336689/10000000000 : ℝ)|^5631 ≤ (40591361393819/100000000000000 : ℝ)^4607
        have hw : |(4782336689/10000000000 : ℝ)|=(4782336689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1852070967/5000000000 : ℝ)|^5631 ≤ (29704320292767/100000000000000 : ℝ)^4607
        have hw : |(1852070967/5000000000 : ℝ)|=(1852070967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(370414173/1000000000 : ℝ)|^5631 ≤ (29704318293229/100000000000000 : ℝ)^4607
        have hw : |(370414173/1000000000 : ℝ)|=(370414173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_12 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-521179133/5000000000 : ℝ)*x 0 + (5654668663/10000000000 : ℝ)*x 1 + (637102657/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521179133/5000000000 : ℝ)^5631 ≤ (3152979965619/50000000000000 : ℝ)^4607 := by
    have hnat : (521179133 : ℕ)^5631*50000000000000^4607 ≤ 3152979965619^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521179133 5000000000 3152979965619 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5654668663/10000000000 : ℝ)^5631 ≤ (9963331597221/20000000000000 : ℝ)^4607 := by
    have hnat : (5654668663 : ℕ)^5631*20000000000000^4607 ≤ 9963331597221^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654668663 10000000000 9963331597221 20000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637102657/1250000000 : ℝ)^5631 ≤ (43877382065357/100000000000000 : ℝ)^4607 := by
    have hnat : (637102657 : ℕ)^5631*100000000000000^4607 ≤ 43877382065357^4607*1250000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637102657 1250000000 43877382065357 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-521179133/5000000000 : ℝ), (5654668663/10000000000 : ℝ), (637102657/1250000000 : ℝ)] ![(3152979965619/50000000000000 : ℝ), (9963331597221/20000000000000 : ℝ), (43877382065357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-521179133/5000000000 : ℝ)|^5631 ≤ (3152979965619/50000000000000 : ℝ)^4607
        have hw : |(-521179133/5000000000 : ℝ)|=(521179133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5654668663/10000000000 : ℝ)|^5631 ≤ (9963331597221/20000000000000 : ℝ)^4607
        have hw : |(5654668663/10000000000 : ℝ)|=(5654668663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637102657/1250000000 : ℝ)|^5631 ≤ (43877382065357/100000000000000 : ℝ)^4607
        have hw : |(637102657/1250000000 : ℝ)|=(637102657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_13 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422641379/10000000000 : ℝ)*x 0 + (-1368177347/10000000000 : ℝ)*x 1 + (5096821847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422641379/10000000000 : ℝ)^5631 ≤ (5916213364443/12500000000000 : ℝ)^4607 := by
    have hnat : (5422641379 : ℕ)^5631*12500000000000^4607 ≤ 5916213364443^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422641379 10000000000 5916213364443 12500000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368177347/10000000000 : ℝ)^5631 ≤ (8792904779639/100000000000000 : ℝ)^4607 := by
    have hnat : (1368177347 : ℕ)^5631*100000000000000^4607 ≤ 8792904779639^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368177347 10000000000 8792904779639 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5096821847/10000000000 : ℝ)^5631 ≤ (43877388284007/100000000000000 : ℝ)^4607 := by
    have hnat : (5096821847 : ℕ)^5631*100000000000000^4607 ≤ 43877388284007^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096821847 10000000000 43877388284007 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422641379/10000000000 : ℝ), (-1368177347/10000000000 : ℝ), (5096821847/10000000000 : ℝ)] ![(5916213364443/12500000000000 : ℝ), (8792904779639/100000000000000 : ℝ), (43877388284007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422641379/10000000000 : ℝ)|^5631 ≤ (5916213364443/12500000000000 : ℝ)^4607
        have hw : |(5422641379/10000000000 : ℝ)|=(5422641379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1368177347/10000000000 : ℝ)|^5631 ≤ (8792904779639/100000000000000 : ℝ)^4607
        have hw : |(-1368177347/10000000000 : ℝ)|=(1368177347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5096821847/10000000000 : ℝ)|^5631 ≤ (43877388284007/100000000000000 : ℝ)^4607
        have hw : |(5096821847/10000000000 : ℝ)|=(5096821847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_14 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1084528289/2000000000 : ℝ)*x 0 + (2548410669/5000000000 : ℝ)*x 1 + (-68408897/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084528289/2000000000 : ℝ)^5631 ≤ (11832426904911/25000000000000 : ℝ)^4607 := by
    have hnat : (1084528289 : ℕ)^5631*25000000000000^4607 ≤ 11832426904911^4607*2000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084528289 2000000000 11832426904911 25000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548410669/5000000000 : ℝ)^5631 ≤ (21938691464091/50000000000000 : ℝ)^4607 := by
    have hnat : (2548410669 : ℕ)^5631*50000000000000^4607 ≤ 21938691464091^4607*5000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548410669 5000000000 21938691464091 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68408897/500000000 : ℝ)^5631 ≤ (4396454718887/50000000000000 : ℝ)^4607 := by
    have hnat : (68408897 : ℕ)^5631*50000000000000^4607 ≤ 4396454718887^4607*500000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68408897 500000000 4396454718887 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084528289/2000000000 : ℝ), (2548410669/5000000000 : ℝ), (-68408897/500000000 : ℝ)] ![(11832426904911/25000000000000 : ℝ), (21938691464091/50000000000000 : ℝ), (4396454718887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084528289/2000000000 : ℝ)|^5631 ≤ (11832426904911/25000000000000 : ℝ)^4607
        have hw : |(1084528289/2000000000 : ℝ)|=(1084528289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548410669/5000000000 : ℝ)|^5631 ≤ (21938691464091/50000000000000 : ℝ)^4607
        have hw : |(2548410669/5000000000 : ℝ)|=(2548410669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68408897/500000000 : ℝ)|^5631 ≤ (4396454718887/50000000000000 : ℝ)^4607
        have hw : |(-68408897/500000000 : ℝ)|=(68408897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1741_box_15 (p : ℝ) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3364033069/10000000000 : ℝ)*x 0 + (4413385021/10000000000 : ℝ)*x 1 + (4413384427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3364033069/10000000000 : ℝ)^5631 ≤ (26405553100387/100000000000000 : ℝ)^4607 := by
    have hnat : (3364033069 : ℕ)^5631*100000000000000^4607 ≤ 26405553100387^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3364033069 10000000000 26405553100387 100000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4413385021/10000000000 : ℝ)^5631 ≤ (18398613235187/50000000000000 : ℝ)^4607 := by
    have hnat : (4413385021 : ℕ)^5631*50000000000000^4607 ≤ 18398613235187^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413385021 10000000000 18398613235187 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4413384427/10000000000 : ℝ)^5631 ≤ (18398610208503/50000000000000 : ℝ)^4607 := by
    have hnat : (4413384427 : ℕ)^5631*50000000000000^4607 ≤ 18398610208503^4607*10000000000^5631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413384427 10000000000 18398610208503 50000000000000 5631 4607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5631/1024 : ℝ)) 5631 4607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3364033069/10000000000 : ℝ), (4413385021/10000000000 : ℝ), (4413384427/10000000000 : ℝ)] ![(26405553100387/100000000000000 : ℝ), (18398613235187/50000000000000 : ℝ), (18398610208503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3364033069/10000000000 : ℝ)|^5631 ≤ (26405553100387/100000000000000 : ℝ)^4607
        have hw : |(3364033069/10000000000 : ℝ)|=(3364033069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4413385021/10000000000 : ℝ)|^5631 ≤ (18398613235187/50000000000000 : ℝ)^4607
        have hw : |(4413385021/10000000000 : ℝ)|=(4413385021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4413384427/10000000000 : ℝ)|^5631 ≤ (18398610208503/50000000000000 : ℝ)^4607
        have hw : |(4413384427/10000000000 : ℝ)|=(4413384427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1741_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2269/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1783/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(68749/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(28831/50000 : ℝ) ∧ (81027/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (92729/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2269/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1783/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2269/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1783/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2269/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1783/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2269/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1783/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2269/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1783/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2269/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1783/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1783/20000 : ℝ) ^ (5615/1024 : ℝ) ≤ (35004754249847/20000000000000000000 : ℝ) := by
    have hpowers : (1783/20000 : ℝ)^5615 ≤ (35004754249847/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1783 : ℕ)^5615*20000000000000000000^1024 ≤ 35004754249847^1024*20000^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1783 20000 35004754249847 20000000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1783/20000 : ℝ)) (X := (35004754249847/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2269/12500 : ℝ) ^ (5615/1024 : ℝ) ≤ (1079686522862939/12500000000000000000 : ℝ) := by
    have hpowers : (2269/12500 : ℝ)^5615 ≤ (1079686522862939/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2269 : ℕ)^5615*12500000000000000000^1024 ≤ 1079686522862939^1024*12500^5615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269 12500 1079686522862939 12500000000000000000 5615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2269/12500 : ℝ)) (X := (1079686522862939/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000035004754249847/10000000000000000000 : ℝ) ≤ (1000000638376083/1000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (10000035004754249847/10000000000000000000 : ℝ)^1024 ≤ (1000000638376083/1000000000000000 : ℝ)^5615 := by
      have hnat : (10000035004754249847 : ℕ)^1024*1000000000000000^5615 ≤ 1000000638376083^5615*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000035004754249847 10000000000000000000 1000000638376083 1000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000638376083/1000000000000000 : ℝ)) (X := (10000035004754249847/10000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008812515954152747/100000000000000000000 : ℝ) ≤ (10000160706878837/10000000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (100008812515954152747/100000000000000000000 : ℝ)^1024 ≤ (10000160706878837/10000000000000000 : ℝ)^5615 := by
      have hnat : (100008812515954152747 : ℕ)^1024*10000000000000000^5615 ≤ 10000160706878837^5615*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008812515954152747 100000000000000000000 10000160706878837 10000000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000160706878837/10000000000000000 : ℝ)) (X := (100008812515954152747/100000000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251079686522862939/6250000000000000000 : ℝ) ≤ (2500078757499211/2500000000000000 : ℝ) ^ (5615/1024 : ℝ) := by
    have hpowers : (6251079686522862939/6250000000000000000 : ℝ)^1024 ≤ (2500078757499211/2500000000000000 : ℝ)^5615 := by
      have hnat : (6251079686522862939 : ℕ)^1024*2500000000000000^5615 ≤ 2500078757499211^5615*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251079686522862939 6250000000000000000 2500078757499211 2500000000000000 1024 5615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500078757499211/2500000000000000 : ℝ)) (X := (6251079686522862939/6250000000000000000 : ℝ)) (by norm_num) 5615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(35004754249847/20000000000000000000 : ℝ) ≤ ((923673073856047219/923700000000000000 : ℝ)+2*(154323118007/923700000000000 : ℝ)*(1783/20000 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (923673073856047219/923700000000000000 : ℝ)+2*(154323118007/923700000000000 : ℝ)*(1783/20000 : ℝ)=(1000000638376083/1000000000000000 : ℝ) by norm_num, show 1+2*(35004754249847/20000000000000000000 : ℝ)=(10000035004754249847/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1079686522862939/12500000000000000000 : ℝ)+(35004754249847/20000000000000000000 : ℝ) ≤ ((923673073856047219/923700000000000000 : ℝ)+(154323118007/923700000000000 : ℝ)*((2269/12500 : ℝ)+(1783/20000 : ℝ)))^(5615/1024 : ℝ) := by
    rw [show (923673073856047219/923700000000000000 : ℝ)+(154323118007/923700000000000 : ℝ)*((2269/12500 : ℝ)+(1783/20000 : ℝ))=(10000160706878837/10000000000000000 : ℝ) by norm_num, show 1+(1079686522862939/12500000000000000000 : ℝ)+(35004754249847/20000000000000000000 : ℝ)=(100008812515954152747/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1079686522862939/12500000000000000000 : ℝ) ≤ ((923673073856047219/923700000000000000 : ℝ)+2*(154323118007/923700000000000 : ℝ)*(2269/12500 : ℝ))^(5615/1024 : ℝ) := by
    rw [show (923673073856047219/923700000000000000 : ℝ)+2*(154323118007/923700000000000 : ℝ)*(2269/12500 : ℝ)=(2500078757499211/2500000000000000 : ℝ) by norm_num, show 1+2*(1079686522862939/12500000000000000000 : ℝ)=(6251079686522862939/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (923673073856047219/923700000000000000 : ℝ)*(X 1 0+X 2 0)+(154323118007/923700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (1783/20000 : ℝ)) (hi := (2269/12500 : ℝ)) (c := (923673073856047219/923700000000000000 : ℝ)) (alpha := (154323118007/923700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (923673073856047219/923700000000000000 : ℝ)*(X 0 1+X 2 1)+(154323118007/923700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (1783/20000 : ℝ)) (hi := (2269/12500 : ℝ)) (c := (923673073856047219/923700000000000000 : ℝ)) (alpha := (154323118007/923700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (923673073856047219/923700000000000000 : ℝ)*(X 0 2+X 1 2)+(154323118007/923700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5615/1024 : ℝ)) (lo := (1783/20000 : ℝ)) (hi := (2269/12500 : ℝ)) (c := (923673073856047219/923700000000000000 : ℝ)) (alpha := (154323118007/923700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-436031343/5000000000 : ℝ)*X 0 0+(2717644989/5000000000 : ℝ)*X 0 1+(1358822529/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5195113703/10000000000 : ℝ)*X 1 0+(-1217140447/10000000000 : ℝ)*X 1 1+(5435290119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1298778289/2500000000 : ℝ)*X 2 0+(5435290507/10000000000 : ℝ)*X 2 1+(-1217140661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((228411649/500000000 : ℝ)*X 0 0+(763300379/2000000000 : ℝ)*X 0 1+(763300531/2000000000 : ℝ)*X 0 2+(228411649/500000000 : ℝ)*X 1 0+(763300379/2000000000 : ℝ)*X 1 1+(763300531/2000000000 : ℝ)*X 1 2+(228411649/500000000 : ℝ)*X 2 0+(763300379/2000000000 : ℝ)*X 2 1+(763300531/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-429206359/2500000000 : ℝ)*X 0 0+(5127245217/10000000000 : ℝ)*X 0 1+(1025449101/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5402125667/10000000000 : ℝ)*X 1 0+(-1355234289/10000000000 : ℝ)*X 1 1+(5127245403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2701062727/5000000000 : ℝ)*X 2 0+(1025449133/2000000000 : ℝ)*X 2 1+(-1355234227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3477022861/10000000000 : ℝ)*X 0 0+(217996461/500000000 : ℝ)*X 0 1+(2179964657/5000000000 : ℝ)*X 0 2+(3477022861/10000000000 : ℝ)*X 1 0+(217996461/500000000 : ℝ)*X 1 1+(2179964657/5000000000 : ℝ)*X 1 2+(3477022861/10000000000 : ℝ)*X 2 0+(217996461/500000000 : ℝ)*X 2 1+(2179964657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1533407181/10000000000 : ℝ)*X 0 0+(2446839383/5000000000 : ℝ)*X 0 1+(5498744113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576264311/5000000000 : ℝ)*X 1 0+(-1187191177/10000000000 : ℝ)*X 1 1+(1099749011/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1288132129/2500000000 : ℝ)*X 2 0+(5498744963/10000000000 : ℝ)*X 2 1+(-1187191453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4782336689/10000000000 : ℝ)*X 0 0+(1852070967/5000000000 : ℝ)*X 0 1+(370414173/1000000000 : ℝ)*X 0 2+(4782336689/10000000000 : ℝ)*X 1 0+(1852070967/5000000000 : ℝ)*X 1 1+(370414173/1000000000 : ℝ)*X 1 2+(4782336689/10000000000 : ℝ)*X 2 0+(1852070967/5000000000 : ℝ)*X 2 1+(370414173/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-521179133/5000000000 : ℝ)*X 0 0+(5654668663/10000000000 : ℝ)*X 0 1+(637102657/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5422641379/10000000000 : ℝ)*X 1 0+(-1368177347/10000000000 : ℝ)*X 1 1+(5096821847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1084528289/2000000000 : ℝ)*X 2 0+(2548410669/5000000000 : ℝ)*X 2 1+(-68408897/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3364033069/10000000000 : ℝ)*X 0 0+(4413385021/10000000000 : ℝ)*X 0 1+(4413384427/10000000000 : ℝ)*X 0 2+(3364033069/10000000000 : ℝ)*X 1 0+(4413385021/10000000000 : ℝ)*X 1 1+(4413384427/10000000000 : ℝ)*X 1 2+(3364033069/10000000000 : ℝ)*X 2 0+(4413385021/10000000000 : ℝ)*X 2 1+(4413384427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1741_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-68749/100000 : ℝ) ≤ (-5291786223744909155393783888763/7697500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3784683/25000000000000 : ℝ)*(lower0) + (47283/625000000000 : ℝ)*(lower2) + (20309623/100000000000000 : ℝ)*(lower3) + (26499121/100000000000000 : ℝ)*(lower4) + (509351608793441/50000000000000 : ℝ)*(major0) + (509351608793441/50000000000000 : ℝ)*(major1) + (509351608793441/50000000000000 : ℝ)*(major2) + (196395325276897/12500000000000 : ℝ)*(sp4) + (1571161194162761/100000000000000 : ℝ)*(sp5) + (785577055482887/50000000000000 : ℝ)*(sp6) + (489158911260877/100000000000000 : ℝ)*(sp7) + (527300147/100000000000000 : ℝ)*(sp12) + (967676281/50000000000000 : ℝ)*(sp13) + (180370991/2000000000000 : ℝ)*(sp14) + (489158911260877/100000000000000 : ℝ)*(f.failure) + (1571163129515323/100000000000000 : ℝ)*(f.sum) + (1308243576772741/46185000000000000000000000000 : ℝ)*base66 + (29840933867375807/15395000000000000000000000000000 : ℝ)*base68 + (148826183919690807/15395000000000000000000000000000 : ℝ)*base70 + (91171936507530807/15395000000000000000000000000000 : ℝ)*base72 + (8633411862271/46185000000000000000000000000 : ℝ)*base74 + (67382803412765807/15395000000000000000000000000000 : ℝ)*base76 + (313410485739125807/15395000000000000000000000000000 : ℝ)*base78 + (121720771800390807/15395000000000000000000000000000 : ℝ)*base80 + (90732851705813/23092500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (102730053/10000000000000000000000 : ℝ)*base89 + (102730053/10000000000000000000000 : ℝ)*base91 + (102730053/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (28831/50000 : ℝ) ≤ (4438724998634315888445614267391/7697500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3500277/25000000000000 : ℝ)*(lower1) + (27927261/100000000000000 : ℝ)*(upper2) + (46963201/100000000000000 : ℝ)*(lower4) + (536669/2500000000000 : ℝ)*(lower5) + (568448451882063/50000000000000 : ℝ)*(major0) + (568448451882063/50000000000000 : ℝ)*(major1) + (568448451882063/50000000000000 : ℝ)*(major2) + (1708657632103347/100000000000000 : ℝ)*(sp0) + (213582237124189/12500000000000 : ℝ)*(sp1) + (854328499896421/50000000000000 : ℝ)*(sp2) + (136478230867493/25000000000000 : ℝ)*(sp3) + (92911469/6250000000000 : ℝ)*(sp5) + (95351367/4000000000000 : ℝ)*(sp6) + (175147367/10000000000000 : ℝ)*(sp12) + (136478230867493/25000000000000 : ℝ)*(f.failure) + (1708659383577017/100000000000000 : ℝ)*(f.sum) + (4045641558177/1924375000000000000000000000 : ℝ)*base66 + (56398655245295401/15395000000000000000000000000000 : ℝ)*base68 + (121486666417115401/15395000000000000000000000000000 : ℝ)*base70 + (9108481263755401/15395000000000000000000000000000 : ℝ)*base72 + (7145183823197/7697500000000000000000000000 : ℝ)*base73 + (57141605382975401/15395000000000000000000000000000 : ℝ)*base76 + (187201346674465401/15395000000000000000000000000000 : ℝ)*base78 + (115292885004030401/15395000000000000000000000000000 : ℝ)*base80 + (28132416925041/15395000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (19414877/2500000000000000000000 : ℝ)*base89 + (19414877/2500000000000000000000 : ℝ)*base91 + (19414877/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (81027/100000 : ℝ) ≤ (779651841875443411359279035069/962187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (17961539/50000000000000 : ℝ)*(upper2) + (47722727/100000000000000 : ℝ)*(upper3) + (600747/10000000000000 : ℝ)*(upper4) + (69075668780849/6250000000000 : ℝ)*(major0) + (69075668780849/6250000000000 : ℝ)*(major1) + (69075668780849/6250000000000 : ℝ)*(major2) + (590401167/100000000000000 : ℝ)*(sp0) + (2200562541/12500000000000 : ℝ)*(sp1) + (14693576309/100000000000000 : ℝ)*(sp2) + (3269940763/100000000000000 : ℝ)*(sp3) + (413178301757373/25000000000000 : ℝ)*(sp8) + (165269619293033/10000000000000 : ℝ)*(sp9) + (33053982077087/2000000000000 : ℝ)*(sp10) + (265347317322097/50000000000000 : ℝ)*(sp11) + (530697904584957/100000000000000 : ℝ)*(f.failure) + (1652713797430659/100000000000000 : ℝ)*(f.sum) + (32150576586071/5773125000000000000000000000 : ℝ)*base65 + (3792696185797919/240546875000000000000000000000 : ℝ)*base67 + (3371664384572699/962187500000000000000000000000 : ℝ)*base70 + (12905483122815227/1924375000000000000000000000000 : ℝ)*base71 + (11493426606913/46185000000000000000000000000 : ℝ)*base73 + (615921028239169/240546875000000000000000000000 : ℝ)*base75 + (1765501496459773/1924375000000000000000000000000 : ℝ)*base78 + (3005502174080227/1924375000000000000000000000000 : ℝ)*base79 + (12860265573661/23092500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (86946827/10000000000000000000000 : ℝ)*base90 + (86946827/10000000000000000000000 : ℝ)*base92 + (86946827/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-92729/100000 : ℝ) ≤ (-14275220963507575901120258418193/15395000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52512851/100000000000000 : ℝ)*(lower0) + (1719767/5000000000000 : ℝ)*(upper3) + (1114227/1562500000000 : ℝ)*(lower4) + (1159148198306951/100000000000000 : ℝ)*(major0) + (1159148198306951/100000000000000 : ℝ)*(major1) + (1159148198306951/100000000000000 : ℝ)*(major2) + (157117521/6250000000000 : ℝ)*(sp0) + (4450251381/100000000000000 : ℝ)*(sp5) + (8995104919/20000000000000 : ℝ)*(sp6) + (4283354917/100000000000000 : ℝ)*(sp7) + (448151289580847/25000000000000 : ℝ)*(sp12) + (224075402744043/12500000000000 : ℝ)*(sp13) + (179256269667913/10000000000000 : ℝ)*(sp14) + (278296611524171/50000000000000 : ℝ)*(sp15) + (556597506403259/100000000000000 : ℝ)*(f.failure) + (71704306888149/4000000000000 : ℝ)*(f.sum) + (38476219462961/23092500000000000000000000000 : ℝ)*base65 + (23351481451934577/30790000000000000000000000000000 : ℝ)*base68 + (191984570528514577/30790000000000000000000000000000 : ℝ)*base70 + (160068160314494577/30790000000000000000000000000000 : ℝ)*base72 + (53371203097333/11546250000000000000000000000 : ℝ)*base73 + (191086013858044577/30790000000000000000000000000000 : ℝ)*base76 + (289827857551324577/30790000000000000000000000000000 : ℝ)*base78 + (36968166914704577/30790000000000000000000000000000 : ℝ)*base80 + (105041134235569/23092500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (76194051/10000000000000000000000 : ℝ)*base89 + (76194051/10000000000000000000000 : ℝ)*base91 + (76194051/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1741_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2269/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1783/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68749/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28831/50000 : ℝ) else (81027/100000 : ℝ) ≤ X j i ∧ X j i ≤ (92729/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1741_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1741_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9077/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68749/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28831/50000 : ℝ) else (81027/100000 : ℝ) ≤ X j i ∧ X j i ≤ (92729/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1741_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1741_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5615/1024 : ℝ) ≤ p) (hpb : p ≤ (5631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (208256089/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9077/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68749/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28831/50000 : ℝ) else (81027/100000 : ℝ) ≤ X j i ∧ X j i ≤ (92729/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1741_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
