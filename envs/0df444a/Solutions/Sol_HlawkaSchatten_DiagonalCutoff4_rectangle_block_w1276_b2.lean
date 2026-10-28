-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1276_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:43.26841+00:00
-- url     : https://prove2.me/submissions/e754ea53-1525-4a90-b542-c128e8691400

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
theorem support_rectangle_w1276_s6_0 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051191863/5000000000 : ℝ)*x 0 + (2708080391/5000000000 : ℝ)*x 1 + (5242299373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051191863/5000000000 : ℝ)^1059 ≤ (12787614367581/100000000000000 : ℝ)^803 := by
    have hnat : (1051191863 : ℕ)^1059*100000000000000^803 ≤ 12787614367581^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051191863 5000000000 12787614367581 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708080391/5000000000 : ℝ)^1059 ≤ (8908841154041/20000000000000 : ℝ)^803 := by
    have hnat : (2708080391 : ℕ)^1059*20000000000000^803 ≤ 8908841154041^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708080391 5000000000 8908841154041 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242299373/10000000000 : ℝ)^1059 ≤ (42668179849831/100000000000000 : ℝ)^803 := by
    have hnat : (5242299373 : ℕ)^1059*100000000000000^803 ≤ 42668179849831^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242299373 10000000000 42668179849831 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051191863/5000000000 : ℝ), (2708080391/5000000000 : ℝ), (5242299373/10000000000 : ℝ)] ![(12787614367581/100000000000000 : ℝ), (8908841154041/20000000000000 : ℝ), (42668179849831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051191863/5000000000 : ℝ)|^1059 ≤ (12787614367581/100000000000000 : ℝ)^803
        have hw : |(-1051191863/5000000000 : ℝ)|=(1051191863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708080391/5000000000 : ℝ)|^1059 ≤ (8908841154041/20000000000000 : ℝ)^803
        have hw : |(2708080391/5000000000 : ℝ)|=(2708080391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242299373/10000000000 : ℝ)|^1059 ≤ (42668179849831/100000000000000 : ℝ)^803
        have hw : |(5242299373/10000000000 : ℝ)|=(5242299373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s6_1 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668754881/1250000000 : ℝ)*x 0 + (-273878139/1250000000 : ℝ)*x 1 + (2621149667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668754881/1250000000 : ℝ)^1059 ≤ (43828431649157/100000000000000 : ℝ)^803 := by
    have hnat : (668754881 : ℕ)^1059*100000000000000^803 ≤ 43828431649157^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668754881 1250000000 43828431649157 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273878139/1250000000 : ℝ)^1059 ≤ (3375847228101/25000000000000 : ℝ)^803 := by
    have hnat : (273878139 : ℕ)^1059*25000000000000^803 ≤ 3375847228101^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273878139 1250000000 3375847228101 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621149667/5000000000 : ℝ)^1059 ≤ (10667044857801/25000000000000 : ℝ)^803 := by
    have hnat : (2621149667 : ℕ)^1059*25000000000000^803 ≤ 10667044857801^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621149667 5000000000 10667044857801 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668754881/1250000000 : ℝ), (-273878139/1250000000 : ℝ), (2621149667/5000000000 : ℝ)] ![(43828431649157/100000000000000 : ℝ), (3375847228101/25000000000000 : ℝ), (10667044857801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668754881/1250000000 : ℝ)|^1059 ≤ (43828431649157/100000000000000 : ℝ)^803
        have hw : |(668754881/1250000000 : ℝ)|=(668754881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273878139/1250000000 : ℝ)|^1059 ≤ (3375847228101/25000000000000 : ℝ)^803
        have hw : |(-273878139/1250000000 : ℝ)|=(273878139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621149667/5000000000 : ℝ)|^1059 ≤ (10667044857801/25000000000000 : ℝ)^803
        have hw : |(2621149667/5000000000 : ℝ)|=(2621149667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s6_2 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (334377437/625000000 : ℝ)*x 0 + (5242299273/10000000000 : ℝ)*x 1 + (-1095512633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334377437/625000000 : ℝ)^1059 ≤ (43828431044141/100000000000000 : ℝ)^803 := by
    have hnat : (334377437 : ℕ)^1059*100000000000000^803 ≤ 43828431044141^803*625000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334377437 625000000 43828431044141 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242299273/10000000000 : ℝ)^1059 ≤ (10667044694107/25000000000000 : ℝ)^803 := by
    have hnat : (5242299273 : ℕ)^1059*25000000000000^803 ≤ 10667044694107^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242299273 10000000000 10667044694107 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095512633/5000000000 : ℝ)^1059 ≤ (13503390164093/100000000000000 : ℝ)^803 := by
    have hnat : (1095512633 : ℕ)^1059*100000000000000^803 ≤ 13503390164093^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095512633 5000000000 13503390164093 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334377437/625000000 : ℝ), (5242299273/10000000000 : ℝ), (-1095512633/5000000000 : ℝ)] ![(43828431044141/100000000000000 : ℝ), (10667044694107/25000000000000 : ℝ), (13503390164093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334377437/625000000 : ℝ)|^1059 ≤ (43828431044141/100000000000000 : ℝ)^803
        have hw : |(334377437/625000000 : ℝ)|=(334377437/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242299273/10000000000 : ℝ)|^1059 ≤ (10667044694107/25000000000000 : ℝ)^803
        have hw : |(5242299273/10000000000 : ℝ)|=(5242299273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095512633/5000000000 : ℝ)|^1059 ≤ (13503390164093/100000000000000 : ℝ)^803
        have hw : |(-1095512633/5000000000 : ℝ)|=(1095512633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s6_3 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4344171583/10000000000 : ℝ)*x 0 + (834018887/2000000000 : ℝ)*x 1 + (565654723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344171583/10000000000 : ℝ)^1059 ≤ (33301982572217/100000000000000 : ℝ)^803 := by
    have hnat : (4344171583 : ℕ)^1059*100000000000000^803 ≤ 33301982572217^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344171583 10000000000 33301982572217 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834018887/2000000000 : ℝ)^1059 ≤ (31553438782863/100000000000000 : ℝ)^803 := by
    have hnat : (834018887 : ℕ)^1059*100000000000000^803 ≤ 31553438782863^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834018887 2000000000 31553438782863 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565654723/1250000000 : ℝ)^1059 ≤ (1757228931429/5000000000000 : ℝ)^803 := by
    have hnat : (565654723 : ℕ)^1059*5000000000000^803 ≤ 1757228931429^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565654723 1250000000 1757228931429 5000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344171583/10000000000 : ℝ), (834018887/2000000000 : ℝ), (565654723/1250000000 : ℝ)] ![(33301982572217/100000000000000 : ℝ), (31553438782863/100000000000000 : ℝ), (1757228931429/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344171583/10000000000 : ℝ)|^1059 ≤ (33301982572217/100000000000000 : ℝ)^803
        have hw : |(4344171583/10000000000 : ℝ)|=(4344171583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834018887/2000000000 : ℝ)|^1059 ≤ (31553438782863/100000000000000 : ℝ)^803
        have hw : |(834018887/2000000000 : ℝ)|=(834018887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565654723/1250000000 : ℝ)|^1059 ≤ (1757228931429/5000000000000 : ℝ)^803
        have hw : |(565654723/1250000000 : ℝ)|=(565654723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s6_4 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102396963/10000000000 : ℝ)*x 0 + (1048583783/2000000000 : ℝ)*x 1 + (2707768919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102396963/10000000000 : ℝ)^1059 ≤ (12787720548863/100000000000000 : ℝ)^803 := by
    have hnat : (2102396963 : ℕ)^1059*100000000000000^803 ≤ 12787720548863^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102396963 10000000000 12787720548863 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048583783/2000000000 : ℝ)^1059 ≤ (42674830156119/100000000000000 : ℝ)^803 := by
    have hnat : (1048583783 : ℕ)^1059*100000000000000^803 ≤ 42674830156119^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048583783 2000000000 42674830156119 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707768919/5000000000 : ℝ)^1059 ≤ (44537449280317/100000000000000 : ℝ)^803 := by
    have hnat : (2707768919 : ℕ)^1059*100000000000000^803 ≤ 44537449280317^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707768919 5000000000 44537449280317 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102396963/10000000000 : ℝ), (1048583783/2000000000 : ℝ), (2707768919/5000000000 : ℝ)] ![(12787720548863/100000000000000 : ℝ), (42674830156119/100000000000000 : ℝ), (44537449280317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102396963/10000000000 : ℝ)|^1059 ≤ (12787720548863/100000000000000 : ℝ)^803
        have hw : |(-2102396963/10000000000 : ℝ)|=(2102396963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048583783/2000000000 : ℝ)|^1059 ≤ (42674830156119/100000000000000 : ℝ)^803
        have hw : |(1048583783/2000000000 : ℝ)|=(1048583783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707768919/5000000000 : ℝ)|^1059 ≤ (44537449280317/100000000000000 : ℝ)^803
        have hw : |(2707768919/5000000000 : ℝ)|=(2707768919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s6_5 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305617057/10000000000 : ℝ)*x 0 + (-2017787059/10000000000 : ℝ)*x 1 + (1353884473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305617057/10000000000 : ℝ)^1059 ≤ (5418642323821/12500000000000 : ℝ)^803 := by
    have hnat : (5305617057 : ℕ)^1059*12500000000000^803 ≤ 5418642323821^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305617057 10000000000 5418642323821 12500000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017787059/10000000000 : ℝ)^1059 ≤ (12113411534633/100000000000000 : ℝ)^803 := by
    have hnat : (2017787059 : ℕ)^1059*100000000000000^803 ≤ 12113411534633^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017787059 10000000000 12113411534633 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353884473/2500000000 : ℝ)^1059 ≤ (22268724932997/50000000000000 : ℝ)^803 := by
    have hnat : (1353884473 : ℕ)^1059*50000000000000^803 ≤ 22268724932997^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353884473 2500000000 22268724932997 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305617057/10000000000 : ℝ), (-2017787059/10000000000 : ℝ), (1353884473/2500000000 : ℝ)] ![(5418642323821/12500000000000 : ℝ), (12113411534633/100000000000000 : ℝ), (22268724932997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305617057/10000000000 : ℝ)|^1059 ≤ (5418642323821/12500000000000 : ℝ)^803
        have hw : |(5305617057/10000000000 : ℝ)|=(5305617057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2017787059/10000000000 : ℝ)|^1059 ≤ (12113411534633/100000000000000 : ℝ)^803
        have hw : |(-2017787059/10000000000 : ℝ)|=(2017787059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353884473/2500000000 : ℝ)|^1059 ≤ (22268724932997/50000000000000 : ℝ)^803
        have hw : |(1353884473/2500000000 : ℝ)|=(1353884473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s6_6 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305617193/10000000000 : ℝ)*x 0 + (1353884467/2500000000 : ℝ)*x 1 + (-1008893453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305617193/10000000000 : ℝ)^1059 ≤ (21674570027997/50000000000000 : ℝ)^803 := by
    have hnat : (5305617193 : ℕ)^1059*50000000000000^803 ≤ 21674570027997^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305617193 10000000000 21674570027997 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353884467/2500000000 : ℝ)^1059 ≤ (44537449605693/100000000000000 : ℝ)^803 := by
    have hnat : (1353884467 : ℕ)^1059*100000000000000^803 ≤ 44537449605693^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353884467 2500000000 44537449605693 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008893453/5000000000 : ℝ)^1059 ≤ (6056705161651/50000000000000 : ℝ)^803 := by
    have hnat : (1008893453 : ℕ)^1059*50000000000000^803 ≤ 6056705161651^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008893453 5000000000 6056705161651 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305617193/10000000000 : ℝ), (1353884467/2500000000 : ℝ), (-1008893453/5000000000 : ℝ)] ![(21674570027997/50000000000000 : ℝ), (44537449605693/100000000000000 : ℝ), (6056705161651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305617193/10000000000 : ℝ)|^1059 ≤ (21674570027997/50000000000000 : ℝ)^803
        have hw : |(5305617193/10000000000 : ℝ)|=(5305617193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353884467/2500000000 : ℝ)|^1059 ≤ (44537449605693/100000000000000 : ℝ)^803
        have hw : |(1353884467/2500000000 : ℝ)|=(1353884467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008893453/5000000000 : ℝ)|^1059 ≤ (6056705161651/50000000000000 : ℝ)^803
        have hw : |(-1008893453/5000000000 : ℝ)|=(1008893453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s6_7 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4344198127/10000000000 : ℝ)*x 0 + (4523971879/10000000000 : ℝ)*x 1 + (2085683373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344198127/10000000000 : ℝ)^1059 ≤ (33302250927609/100000000000000 : ℝ)^803 := by
    have hnat : (4344198127 : ℕ)^1059*100000000000000^803 ≤ 33302250927609^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344198127 10000000000 33302250927609 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523971879/10000000000 : ℝ)^1059 ≤ (1405264537289/4000000000000 : ℝ)^803 := by
    have hnat : (4523971879 : ℕ)^1059*4000000000000^803 ≤ 1405264537289^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523971879 10000000000 1405264537289 4000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085683373/5000000000 : ℝ)^1059 ≤ (31566135622171/100000000000000 : ℝ)^803 := by
    have hnat : (2085683373 : ℕ)^1059*100000000000000^803 ≤ 31566135622171^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085683373 5000000000 31566135622171 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344198127/10000000000 : ℝ), (4523971879/10000000000 : ℝ), (2085683373/5000000000 : ℝ)] ![(33302250927609/100000000000000 : ℝ), (1405264537289/4000000000000 : ℝ), (31566135622171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344198127/10000000000 : ℝ)|^1059 ≤ (33302250927609/100000000000000 : ℝ)^803
        have hw : |(4344198127/10000000000 : ℝ)|=(4344198127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523971879/10000000000 : ℝ)|^1059 ≤ (1405264537289/4000000000000 : ℝ)^803
        have hw : |(4523971879/10000000000 : ℝ)|=(4523971879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085683373/5000000000 : ℝ)|^1059 ≤ (31566135622171/100000000000000 : ℝ)^803
        have hw : |(2085683373/5000000000 : ℝ)|=(2085683373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1276_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10971/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1373/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14663/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10971/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10971/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10971/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10971/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10971/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10971/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10971/100000 : ℝ) ^ (4235/1024 : ℝ) ≤ (1073262071750473/10000000000000000000 : ℝ) := by
    have hpowers : (10971/100000 : ℝ)^4235 ≤ (1073262071750473/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10971 : ℕ)^4235*10000000000000000000^1024 ≤ 1073262071750473^1024*100000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10971 100000 1073262071750473 10000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10971/100000 : ℝ)) (X := (1073262071750473/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14677/100000 : ℝ) ^ (4235/1024 : ℝ) ≤ (35762403609951373/100000000000000000000 : ℝ) := by
    have hpowers : (14677/100000 : ℝ)^4235 ≤ (35762403609951373/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14677 : ℕ)^4235*100000000000000000000^1024 ≤ 35762403609951373^1024*100000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14677 100000 35762403609951373 100000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14677/100000 : ℝ)) (X := (35762403609951373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001073262071750473/5000000000000000000 : ℝ) ≤ (10000518975650341/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (5001073262071750473/5000000000000000000 : ℝ)^1024 ≤ (10000518975650341/10000000000000000 : ℝ)^4235 := by
      have hnat : (5001073262071750473 : ℕ)^1024*10000000000000000^4235 ≤ 10000518975650341^4235*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001073262071750473 5000000000000000000 10000518975650341 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000518975650341/10000000000000000 : ℝ)) (X := (5001073262071750473/5000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046495024327456103/100000000000000000000 : ℝ) ≤ (100011240263309/100000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (100046495024327456103/100000000000000000000 : ℝ)^1024 ≤ (100011240263309/100000000000000 : ℝ)^4235 := by
      have hnat : (100046495024327456103 : ℕ)^1024*100000000000000^4235 ≤ 100011240263309^4235*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046495024327456103 100000000000000000000 100011240263309 100000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100011240263309/100000000000000 : ℝ)) (X := (100046495024327456103/100000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035762403609951373/50000000000000000000 : ℝ) ≤ (10001729077011459/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (50035762403609951373/50000000000000000000 : ℝ)^1024 ≤ (10001729077011459/10000000000000000 : ℝ)^4235 := by
      have hnat : (50035762403609951373 : ℕ)^1024*10000000000000000^4235 ≤ 10001729077011459^4235*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035762403609951373 50000000000000000000 10001729077011459 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001729077011459/10000000000000000 : ℝ)) (X := (50035762403609951373/50000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1073262071750473/10000000000000000000 : ℝ) ≤ ((4631080912715917271/4632500000000000000 : ℝ)+2*(605050680559/370600000000000 : ℝ)*(10971/100000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (4631080912715917271/4632500000000000000 : ℝ)+2*(605050680559/370600000000000 : ℝ)*(10971/100000 : ℝ)=(10000518975650341/10000000000000000 : ℝ) by norm_num, show 1+2*(1073262071750473/10000000000000000000 : ℝ)=(5001073262071750473/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35762403609951373/100000000000000000000 : ℝ)+(1073262071750473/10000000000000000000 : ℝ) ≤ ((4631080912715917271/4632500000000000000 : ℝ)+(605050680559/370600000000000 : ℝ)*((14677/100000 : ℝ)+(10971/100000 : ℝ)))^(4235/1024 : ℝ) := by
    rw [show (4631080912715917271/4632500000000000000 : ℝ)+(605050680559/370600000000000 : ℝ)*((14677/100000 : ℝ)+(10971/100000 : ℝ))=(100011240263309/100000000000000 : ℝ) by norm_num, show 1+(35762403609951373/100000000000000000000 : ℝ)+(1073262071750473/10000000000000000000 : ℝ)=(100046495024327456103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35762403609951373/100000000000000000000 : ℝ) ≤ ((4631080912715917271/4632500000000000000 : ℝ)+2*(605050680559/370600000000000 : ℝ)*(14677/100000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (4631080912715917271/4632500000000000000 : ℝ)+2*(605050680559/370600000000000 : ℝ)*(14677/100000 : ℝ)=(10001729077011459/10000000000000000 : ℝ) by norm_num, show 1+2*(35762403609951373/100000000000000000000 : ℝ)=(50035762403609951373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4631080912715917271/4632500000000000000 : ℝ)*(X 1 0+X 2 0)+(605050680559/370600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (10971/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (4631080912715917271/4632500000000000000 : ℝ)) (alpha := (605050680559/370600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4631080912715917271/4632500000000000000 : ℝ)*(X 0 1+X 2 1)+(605050680559/370600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (10971/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (4631080912715917271/4632500000000000000 : ℝ)) (alpha := (605050680559/370600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4631080912715917271/4632500000000000000 : ℝ)*(X 0 2+X 1 2)+(605050680559/370600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (10971/100000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (4631080912715917271/4632500000000000000 : ℝ)) (alpha := (605050680559/370600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1051191863/5000000000 : ℝ)*X 0 0+(2708080391/5000000000 : ℝ)*X 0 1+(5242299373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668754881/1250000000 : ℝ)*X 1 0+(-273878139/1250000000 : ℝ)*X 1 1+(2621149667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334377437/625000000 : ℝ)*X 2 0+(5242299273/10000000000 : ℝ)*X 2 1+(-1095512633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4344171583/10000000000 : ℝ)*X 0 0+(834018887/2000000000 : ℝ)*X 0 1+(565654723/1250000000 : ℝ)*X 0 2+(4344171583/10000000000 : ℝ)*X 1 0+(834018887/2000000000 : ℝ)*X 1 1+(565654723/1250000000 : ℝ)*X 1 2+(4344171583/10000000000 : ℝ)*X 2 0+(834018887/2000000000 : ℝ)*X 2 1+(565654723/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2102396963/10000000000 : ℝ)*X 0 0+(1048583783/2000000000 : ℝ)*X 0 1+(2707768919/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305617057/10000000000 : ℝ)*X 1 0+(-2017787059/10000000000 : ℝ)*X 1 1+(1353884473/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305617193/10000000000 : ℝ)*X 2 0+(1353884467/2500000000 : ℝ)*X 2 1+(-1008893453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4344198127/10000000000 : ℝ)*X 0 0+(4523971879/10000000000 : ℝ)*X 0 1+(2085683373/5000000000 : ℝ)*X 0 2+(4344198127/10000000000 : ℝ)*X 1 0+(4523971879/10000000000 : ℝ)*X 1 1+(2085683373/5000000000 : ℝ)*X 1 2+(4344198127/10000000000 : ℝ)*X 2 0+(4523971879/10000000000 : ℝ)*X 2 1+(2085683373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41718562846414434808481379/6812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15835517/1250000000000 : ℝ)*(base19) + (2021573/156250000000 : ℝ)*(base23) + (57124299/100000000000000 : ℝ)*(lower2) + (25794201/20000000000000 : ℝ)*(upper3) + (6485047/6250000000000 : ℝ)*(lower4) + (4283780437848659/100000000000000 : ℝ)*(major0) + (4283780437848659/100000000000000 : ℝ)*(major1) + (214189021892433/5000000000000 : ℝ)*(major2) + (5751739675756551/100000000000000 : ℝ)*(sp0) + (718970557624919/12500000000000 : ℝ)*(sp1) + (718970554254249/12500000000000 : ℝ)*(sp2) + (1407889482138237/50000000000000 : ℝ)*(sp3) + (26052084161/100000000000000 : ℝ)*(sp4) + (15979452599/100000000000000 : ℝ)*(sp7) + (1407897471864537/50000000000000 : ℝ)*(f.failure) + (718970715980089/12500000000000 : ℝ)*(f.sum) + (135430179218561/37060000000000000000000000000 : ℝ)*base65 + (3904998244693039589/463250000000000000000000000000000 : ℝ)*base67 + (1652944345868463/170312500000000000000000000000 : ℝ)*base69 + (1508724863253289589/463250000000000000000000000000000 : ℝ)*base71 + (106881751605101/37060000000000000000000000000 : ℝ)*base73 + (3748665382852551/340625000000000000000000000000 : ℝ)*base75 + (4859391075170302089/463250000000000000000000000000000 : ℝ)*base77 + (2908720812684302089/463250000000000000000000000000000 : ℝ)*base79 + (99953166719441/18530000000000000000000000000 : ℝ)*base81 + (62970131/5000000000000000000000 : ℝ)*base89 + (62970131/5000000000000000000000 : ℝ)*base91 + (12970131/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6541354672923869592541953/1809570312500000000000000000000 : ℝ) := by norm_num
    linear_combination (21781009/6250000000000 : ℝ)*(base19) + (278870737/50000000000000 : ℝ)*(base23) + (29452471/25000000000000 : ℝ)*(upper3) + (943577/25000000000000 : ℝ)*(lower4) + (106686437/100000000000000 : ℝ)*(upper5) + (134830363277437/3125000000000 : ℝ)*(major0) + (134830363277437/3125000000000 : ℝ)*(major1) + (134830363277437/3125000000000 : ℝ)*(major2) + (33821403/800000000000 : ℝ)*(sp1) + (212675569/2000000000000 : ℝ)*(sp2) + (181034645732921/3125000000000 : ℝ)*(sp4) + (2896552043640977/50000000000000 : ℝ)*(sp5) + (1448274367983387/25000000000000 : ℝ)*(sp6) + (88626077056467/3125000000000 : ℝ)*(sp7) + (88626077056467/3125000000000 : ℝ)*(f.failure) + (181034645732921/3125000000000 : ℝ)*(f.sum) + (583535554703/579062500000000000000000000 : ℝ)*base65 + (13932887577048073/14476562500000000000000000000000 : ℝ)*base68 + (199587666199798073/14476562500000000000000000000000 : ℝ)*base70 + (3881311778094349/7238281250000000000000000000000 : ℝ)*base72 + (10992757994161/4632500000000000000000000000 : ℝ)*base74 + (205016928001250599/7238281250000000000000000000000 : ℝ)*base76 + (41705516315233177/14476562500000000000000000000000 : ℝ)*base77 + (198639313483063099/7238281250000000000000000000000 : ℝ)*base80 + (8229939759253/2316250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (511279/312500000000000000000 : ℝ)*base90 + (511279/312500000000000000000 : ℝ)*base92 + (511279/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1276_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10971/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1276_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1276_s7_0 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051199249/5000000000 : ℝ)*x 0 + (2708017761/5000000000 : ℝ)*x 1 + (2621207451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051199249/5000000000 : ℝ)^1059 ≤ (12787732861959/100000000000000 : ℝ)^803 := by
    have hnat : (1051199249 : ℕ)^1059*100000000000000^803 ≤ 12787732861959^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051199249 5000000000 12787732861959 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708017761/5000000000 : ℝ)^1059 ≤ (44542847172449/100000000000000 : ℝ)^803 := by
    have hnat : (2708017761 : ℕ)^1059*100000000000000^803 ≤ 44542847172449^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708017761 5000000000 44542847172449 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621207451/5000000000 : ℝ)^1059 ≤ (21334709972839/50000000000000 : ℝ)^803 := by
    have hnat : (2621207451 : ℕ)^1059*50000000000000^803 ≤ 21334709972839^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621207451 5000000000 21334709972839 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051199249/5000000000 : ℝ), (2708017761/5000000000 : ℝ), (2621207451/5000000000 : ℝ)] ![(12787732861959/100000000000000 : ℝ), (44542847172449/100000000000000 : ℝ), (21334709972839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051199249/5000000000 : ℝ)|^1059 ≤ (12787732861959/100000000000000 : ℝ)^803
        have hw : |(-1051199249/5000000000 : ℝ)|=(1051199249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708017761/5000000000 : ℝ)|^1059 ≤ (44542847172449/100000000000000 : ℝ)^803
        have hw : |(2708017761/5000000000 : ℝ)|=(2708017761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621207451/5000000000 : ℝ)|^1059 ≤ (21334709972839/50000000000000 : ℝ)^803
        have hw : |(2621207451/5000000000 : ℝ)|=(2621207451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s7_1 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337501649/2500000000 : ℝ)*x 0 + (-2190915653/10000000000 : ℝ)*x 1 + (2621207439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337501649/2500000000 : ℝ)^1059 ≤ (1369627532571/3125000000000 : ℝ)^803 := by
    have hnat : (1337501649 : ℕ)^1059*3125000000000^803 ≤ 1369627532571^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337501649 2500000000 1369627532571 3125000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190915653/10000000000 : ℝ)^1059 ≤ (13502499252837/100000000000000 : ℝ)^803 := by
    have hnat : (2190915653 : ℕ)^1059*100000000000000^803 ≤ 13502499252837^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190915653 10000000000 13502499252837 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621207439/5000000000 : ℝ)^1059 ≤ (42669419688059/100000000000000 : ℝ)^803 := by
    have hnat : (2621207439 : ℕ)^1059*100000000000000^803 ≤ 42669419688059^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621207439 5000000000 42669419688059 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337501649/2500000000 : ℝ), (-2190915653/10000000000 : ℝ), (2621207439/5000000000 : ℝ)] ![(1369627532571/3125000000000 : ℝ), (13502499252837/100000000000000 : ℝ), (42669419688059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337501649/2500000000 : ℝ)|^1059 ≤ (1369627532571/3125000000000 : ℝ)^803
        have hw : |(1337501649/2500000000 : ℝ)|=(1337501649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190915653/10000000000 : ℝ)|^1059 ≤ (13502499252837/100000000000000 : ℝ)^803
        have hw : |(-2190915653/10000000000 : ℝ)|=(2190915653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621207439/5000000000 : ℝ)|^1059 ≤ (42669419688059/100000000000000 : ℝ)^803
        have hw : |(2621207439/5000000000 : ℝ)|=(2621207439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s7_2 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1070001281/2000000000 : ℝ)*x 0 + (524241473/1000000000 : ℝ)*x 1 + (-2190916103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070001281/2000000000 : ℝ)^1059 ≤ (43828078978737/100000000000000 : ℝ)^803 := by
    have hnat : (1070001281 : ℕ)^1059*100000000000000^803 ≤ 43828078978737^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070001281 2000000000 43828078978737 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524241473/1000000000 : ℝ)^1059 ≤ (10667354524853/25000000000000 : ℝ)^803 := by
    have hnat : (524241473 : ℕ)^1059*25000000000000^803 ≤ 10667354524853^803*1000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524241473 1000000000 10667354524853 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190916103/10000000000 : ℝ)^1059 ≤ (13502502910313/100000000000000 : ℝ)^803 := by
    have hnat : (2190916103 : ℕ)^1059*100000000000000^803 ≤ 13502502910313^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190916103 10000000000 13502502910313 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070001281/2000000000 : ℝ), (524241473/1000000000 : ℝ), (-2190916103/10000000000 : ℝ)] ![(43828078978737/100000000000000 : ℝ), (10667354524853/25000000000000 : ℝ), (13502502910313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070001281/2000000000 : ℝ)|^1059 ≤ (43828078978737/100000000000000 : ℝ)^803
        have hw : |(1070001281/2000000000 : ℝ)|=(1070001281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524241473/1000000000 : ℝ)|^1059 ≤ (10667354524853/25000000000000 : ℝ)^803
        have hw : |(524241473/1000000000 : ℝ)|=(524241473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190916103/10000000000 : ℝ)|^1059 ≤ (13502502910313/100000000000000 : ℝ)^803
        have hw : |(-2190916103/10000000000 : ℝ)|=(2190916103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s7_3 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2172089567/5000000000 : ℝ)*x 0 + (4170340163/10000000000 : ℝ)*x 1 + (4524990919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172089567/5000000000 : ℝ)^1059 ≤ (8325514727877/25000000000000 : ℝ)^803 := by
    have hnat : (2172089567 : ℕ)^1059*25000000000000^803 ≤ 8325514727877^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172089567 5000000000 8325514727877 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170340163/10000000000 : ℝ)^1059 ≤ (15777945446427/50000000000000 : ℝ)^803 := by
    have hnat : (4170340163 : ℕ)^1059*50000000000000^803 ≤ 15777945446427^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170340163 10000000000 15777945446427 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524990919/10000000000 : ℝ)^1059 ≤ (35142050186001/100000000000000 : ℝ)^803 := by
    have hnat : (4524990919 : ℕ)^1059*100000000000000^803 ≤ 35142050186001^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524990919 10000000000 35142050186001 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172089567/5000000000 : ℝ), (4170340163/10000000000 : ℝ), (4524990919/10000000000 : ℝ)] ![(8325514727877/25000000000000 : ℝ), (15777945446427/50000000000000 : ℝ), (35142050186001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172089567/5000000000 : ℝ)|^1059 ≤ (8325514727877/25000000000000 : ℝ)^803
        have hw : |(2172089567/5000000000 : ℝ)|=(2172089567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170340163/10000000000 : ℝ)|^1059 ≤ (15777945446427/50000000000000 : ℝ)^803
        have hw : |(4170340163/10000000000 : ℝ)|=(4170340163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524990919/10000000000 : ℝ)|^1059 ≤ (35142050186001/100000000000000 : ℝ)^803
        have hw : |(4524990919/10000000000 : ℝ)|=(4524990919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s7_4 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051205999/5000000000 : ℝ)*x 0 + (1310758151/2500000000 : ℝ)*x 1 + (5415414197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051205999/5000000000 : ℝ)^1059 ≤ (6393920576577/50000000000000 : ℝ)^803 := by
    have hnat : (1051205999 : ℕ)^1059*50000000000000^803 ≤ 6393920576577^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051205999 5000000000 6393920576577 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310758151/2500000000 : ℝ)^1059 ≤ (42676050547193/100000000000000 : ℝ)^803 := by
    have hnat : (1310758151 : ℕ)^1059*100000000000000^803 ≤ 42676050547193^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310758151 2500000000 42676050547193 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415414197/10000000000 : ℝ)^1059 ≤ (22268054145853/50000000000000 : ℝ)^803 := by
    have hnat : (5415414197 : ℕ)^1059*50000000000000^803 ≤ 22268054145853^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415414197 10000000000 22268054145853 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051205999/5000000000 : ℝ), (1310758151/2500000000 : ℝ), (5415414197/10000000000 : ℝ)] ![(6393920576577/50000000000000 : ℝ), (42676050547193/100000000000000 : ℝ), (22268054145853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051205999/5000000000 : ℝ)|^1059 ≤ (6393920576577/50000000000000 : ℝ)^803
        have hw : |(-1051205999/5000000000 : ℝ)|=(1051205999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310758151/2500000000 : ℝ)|^1059 ≤ (42676050547193/100000000000000 : ℝ)^803
        have hw : |(1310758151/2500000000 : ℝ)|=(1310758151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415414197/10000000000 : ℝ)|^1059 ≤ (22268054145853/50000000000000 : ℝ)^803
        have hw : |(5415414197/10000000000 : ℝ)|=(5415414197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s7_5 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305646881/10000000000 : ℝ)*x 0 + (-1008957959/5000000000 : ℝ)*x 1 + (5415414197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305646881/10000000000 : ℝ)^1059 ≤ (43349459950159/100000000000000 : ℝ)^803 := by
    have hnat : (5305646881 : ℕ)^1059*100000000000000^803 ≤ 43349459950159^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305646881 10000000000 43349459950159 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008957959/5000000000 : ℝ)^1059 ≤ (3028607936837/25000000000000 : ℝ)^803 := by
    have hnat : (1008957959 : ℕ)^1059*25000000000000^803 ≤ 3028607936837^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008957959 5000000000 3028607936837 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415414197/10000000000 : ℝ)^1059 ≤ (22268054145853/50000000000000 : ℝ)^803 := by
    have hnat : (5415414197 : ℕ)^1059*50000000000000^803 ≤ 22268054145853^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415414197 10000000000 22268054145853 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305646881/10000000000 : ℝ), (-1008957959/5000000000 : ℝ), (5415414197/10000000000 : ℝ)] ![(43349459950159/100000000000000 : ℝ), (3028607936837/25000000000000 : ℝ), (22268054145853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305646881/10000000000 : ℝ)|^1059 ≤ (43349459950159/100000000000000 : ℝ)^803
        have hw : |(5305646881/10000000000 : ℝ)|=(5305646881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1008957959/5000000000 : ℝ)|^1059 ≤ (3028607936837/25000000000000 : ℝ)^803
        have hw : |(-1008957959/5000000000 : ℝ)|=(1008957959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415414197/10000000000 : ℝ)|^1059 ≤ (22268054145853/50000000000000 : ℝ)^803
        have hw : |(5415414197/10000000000 : ℝ)|=(5415414197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s7_6 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305646881/10000000000 : ℝ)*x 0 + (5415414197/10000000000 : ℝ)*x 1 + (-1008957959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305646881/10000000000 : ℝ)^1059 ≤ (43349459950159/100000000000000 : ℝ)^803 := by
    have hnat : (5305646881 : ℕ)^1059*100000000000000^803 ≤ 43349459950159^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305646881 10000000000 43349459950159 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415414197/10000000000 : ℝ)^1059 ≤ (22268054145853/50000000000000 : ℝ)^803 := by
    have hnat : (5415414197 : ℕ)^1059*50000000000000^803 ≤ 22268054145853^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415414197 10000000000 22268054145853 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008957959/5000000000 : ℝ)^1059 ≤ (3028607936837/25000000000000 : ℝ)^803 := by
    have hnat : (1008957959 : ℕ)^1059*25000000000000^803 ≤ 3028607936837^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008957959 5000000000 3028607936837 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305646881/10000000000 : ℝ), (5415414197/10000000000 : ℝ), (-1008957959/5000000000 : ℝ)] ![(43349459950159/100000000000000 : ℝ), (22268054145853/50000000000000 : ℝ), (3028607936837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305646881/10000000000 : ℝ)|^1059 ≤ (43349459950159/100000000000000 : ℝ)^803
        have hw : |(5305646881/10000000000 : ℝ)|=(5305646881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415414197/10000000000 : ℝ)|^1059 ≤ (22268054145853/50000000000000 : ℝ)^803
        have hw : |(5415414197/10000000000 : ℝ)|=(5415414197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008957959/5000000000 : ℝ)|^1059 ≤ (3028607936837/25000000000000 : ℝ)^803
        have hw : |(-1008957959/5000000000 : ℝ)|=(1008957959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s7_7 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4344206499/10000000000 : ℝ)*x 0 + (1130932103/2500000000 : ℝ)*x 1 + (1042902027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344206499/10000000000 : ℝ)^1059 ≤ (16651167783617/50000000000000 : ℝ)^803 := by
    have hnat : (4344206499 : ℕ)^1059*50000000000000^803 ≤ 16651167783617^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344206499 10000000000 16651167783617 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130932103/2500000000 : ℝ)^1059 ≤ (8782280003697/25000000000000 : ℝ)^803 := by
    have hnat : (1130932103 : ℕ)^1059*25000000000000^803 ≤ 8782280003697^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130932103 2500000000 8782280003697 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042902027/2500000000 : ℝ)^1059 ≤ (15784272198931/50000000000000 : ℝ)^803 := by
    have hnat : (1042902027 : ℕ)^1059*50000000000000^803 ≤ 15784272198931^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042902027 2500000000 15784272198931 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344206499/10000000000 : ℝ), (1130932103/2500000000 : ℝ), (1042902027/2500000000 : ℝ)] ![(16651167783617/50000000000000 : ℝ), (8782280003697/25000000000000 : ℝ), (15784272198931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344206499/10000000000 : ℝ)|^1059 ≤ (16651167783617/50000000000000 : ℝ)^803
        have hw : |(4344206499/10000000000 : ℝ)|=(4344206499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130932103/2500000000 : ℝ)|^1059 ≤ (8782280003697/25000000000000 : ℝ)^803
        have hw : |(1130932103/2500000000 : ℝ)|=(1130932103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042902027/2500000000 : ℝ)|^1059 ≤ (15784272198931/50000000000000 : ℝ)^803
        have hw : |(1042902027/2500000000 : ℝ)|=(1042902027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1276_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5493/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14661/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1373/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1373/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1373/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1373/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1373/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1373/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1373/12500 : ℝ) ^ (4235/1024 : ℝ) ≤ (10785314958877517/100000000000000000000 : ℝ) := by
    have hpowers : (1373/12500 : ℝ)^4235 ≤ (10785314958877517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1373 : ℕ)^4235*100000000000000000000^1024 ≤ 10785314958877517^1024*12500^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1373 12500 10785314958877517 100000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1373/12500 : ℝ)) (X := (10785314958877517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14663/100000 : ℝ) ^ (4235/1024 : ℝ) ≤ (17810766345799019/50000000000000000000 : ℝ) := by
    have hpowers : (14663/100000 : ℝ)^4235 ≤ (17810766345799019/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14663 : ℕ)^4235*50000000000000000000^1024 ≤ 17810766345799019^1024*100000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14663 100000 17810766345799019 50000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14663/100000 : ℝ)) (X := (17810766345799019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010785314958877517/50000000000000000000 : ℝ) ≤ (10000521523470951/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (50010785314958877517/50000000000000000000 : ℝ)^1024 ≤ (10000521523470951/10000000000000000 : ℝ)^4235 := by
      have hnat : (50010785314958877517 : ℕ)^1024*10000000000000000^4235 ≤ 10000521523470951^4235*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010785314958877517 50000000000000000000 10000521523470951 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000521523470951/10000000000000000 : ℝ)) (X := (50010785314958877517/50000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009281369530095111/20000000000000000000 : ℝ) ≤ (10001121895017331/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (20009281369530095111/20000000000000000000 : ℝ)^1024 ≤ (10001121895017331/10000000000000000 : ℝ)^4235 := by
      have hnat : (20009281369530095111 : ℕ)^1024*10000000000000000^4235 ≤ 10001121895017331^4235*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009281369530095111 20000000000000000000 10001121895017331 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001121895017331/10000000000000000 : ℝ)) (X := (20009281369530095111/20000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017810766345799019/25000000000000000000 : ℝ) ≤ (10001722266563711/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (25017810766345799019/25000000000000000000 : ℝ)^1024 ≤ (10001722266563711/10000000000000000 : ℝ)^4235 := by
      have hnat : (25017810766345799019 : ℕ)^1024*10000000000000000^4235 ≤ 10001722266563711^4235*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017810766345799019 25000000000000000000 10001722266563711 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001722266563711/10000000000000000 : ℝ)) (X := (25017810766345799019/25000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10785314958877517/100000000000000000000 : ℝ) ≤ ((36778729722718752889/36790000000000000000 : ℝ)+2*(30018577319/18395000000000 : ℝ)*(1373/12500 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (36778729722718752889/36790000000000000000 : ℝ)+2*(30018577319/18395000000000 : ℝ)*(1373/12500 : ℝ)=(10000521523470951/10000000000000000 : ℝ) by norm_num, show 1+2*(10785314958877517/100000000000000000000 : ℝ)=(50010785314958877517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17810766345799019/50000000000000000000 : ℝ)+(10785314958877517/100000000000000000000 : ℝ) ≤ ((36778729722718752889/36790000000000000000 : ℝ)+(30018577319/18395000000000 : ℝ)*((14663/100000 : ℝ)+(1373/12500 : ℝ)))^(4235/1024 : ℝ) := by
    rw [show (36778729722718752889/36790000000000000000 : ℝ)+(30018577319/18395000000000 : ℝ)*((14663/100000 : ℝ)+(1373/12500 : ℝ))=(10001121895017331/10000000000000000 : ℝ) by norm_num, show 1+(17810766345799019/50000000000000000000 : ℝ)+(10785314958877517/100000000000000000000 : ℝ)=(20009281369530095111/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17810766345799019/50000000000000000000 : ℝ) ≤ ((36778729722718752889/36790000000000000000 : ℝ)+2*(30018577319/18395000000000 : ℝ)*(14663/100000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (36778729722718752889/36790000000000000000 : ℝ)+2*(30018577319/18395000000000 : ℝ)*(14663/100000 : ℝ)=(10001722266563711/10000000000000000 : ℝ) by norm_num, show 1+2*(17810766345799019/50000000000000000000 : ℝ)=(25017810766345799019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36778729722718752889/36790000000000000000 : ℝ)*(X 1 0+X 2 0)+(30018577319/18395000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (36778729722718752889/36790000000000000000 : ℝ)) (alpha := (30018577319/18395000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36778729722718752889/36790000000000000000 : ℝ)*(X 0 1+X 2 1)+(30018577319/18395000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (36778729722718752889/36790000000000000000 : ℝ)) (alpha := (30018577319/18395000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36778729722718752889/36790000000000000000 : ℝ)*(X 0 2+X 1 2)+(30018577319/18395000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (36778729722718752889/36790000000000000000 : ℝ)) (alpha := (30018577319/18395000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1051199249/5000000000 : ℝ)*X 0 0+(2708017761/5000000000 : ℝ)*X 0 1+(2621207451/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337501649/2500000000 : ℝ)*X 1 0+(-2190915653/10000000000 : ℝ)*X 1 1+(2621207439/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070001281/2000000000 : ℝ)*X 2 0+(524241473/1000000000 : ℝ)*X 2 1+(-2190916103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2172089567/5000000000 : ℝ)*X 0 0+(4170340163/10000000000 : ℝ)*X 0 1+(4524990919/10000000000 : ℝ)*X 0 2+(2172089567/5000000000 : ℝ)*X 1 0+(4170340163/10000000000 : ℝ)*X 1 1+(4524990919/10000000000 : ℝ)*X 1 2+(2172089567/5000000000 : ℝ)*X 2 0+(4170340163/10000000000 : ℝ)*X 2 1+(4524990919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1051205999/5000000000 : ℝ)*X 0 0+(1310758151/2500000000 : ℝ)*X 0 1+(5415414197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305646881/10000000000 : ℝ)*X 1 0+(-1008957959/5000000000 : ℝ)*X 1 1+(5415414197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305646881/10000000000 : ℝ)*X 2 0+(5415414197/10000000000 : ℝ)*X 2 1+(-1008957959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4344206499/10000000000 : ℝ)*X 0 0+(1130932103/2500000000 : ℝ)*X 0 1+(1042902027/2500000000 : ℝ)*X 0 2+(4344206499/10000000000 : ℝ)*X 1 0+(1130932103/2500000000 : ℝ)*X 1 1+(1042902027/2500000000 : ℝ)*X 1 2+(4344206499/10000000000 : ℝ)*X 2 0+(1130932103/2500000000 : ℝ)*X 2 1+(1042902027/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15652329436938609489074105037/919750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387482277/100000000000000 : ℝ)*(base19) + (89392119/20000000000000 : ℝ)*(base23) + (7533313/20000000000000 : ℝ)*(upper3) + (2238651/1250000000000 : ℝ)*(lower4) + (2144847627679111/50000000000000 : ℝ)*(major0) + (2144847627679111/50000000000000 : ℝ)*(major1) + (2144847627679111/50000000000000 : ℝ)*(major2) + (5759699419263979/100000000000000 : ℝ)*(sp0) + (5759706711473697/100000000000000 : ℝ)*(sp1) + (5759698252278831/100000000000000 : ℝ)*(sp2) + (2819679985375017/100000000000000 : ℝ)*(sp3) + (3839845997/50000000000000 : ℝ)*(sp4) + (8399716547/100000000000000 : ℝ)*(sp6) + (2859117913/100000000000000 : ℝ)*(sp7) + (281968284449293/10000000000000 : ℝ)*(f.failure) + (5759707098955973/100000000000000 : ℝ)*(f.sum) + (14269521767103/3679000000000000000000000000 : ℝ)*base65 + (14810984541944701679/1839500000000000000000000000000000 : ℝ)*base67 + (8466189661754298321/1839500000000000000000000000000000 : ℝ)*base70 + (422339764827298321/1839500000000000000000000000000000 : ℝ)*base72 + (2315071343789/1839500000000000000000000000 : ℝ)*base73 + (8801365122309298321/1839500000000000000000000000000000 : ℝ)*base76 + (5462656313302298321/1839500000000000000000000000000000 : ℝ)*base78 + (24887096009932201679/1839500000000000000000000000000000 : ℝ)*base79 + (23666233969/11496875000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3361841/1000000000000000000000 : ℝ)*base90 + (3361841/1000000000000000000000 : ℝ)*base92 + (3361841/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1050911500834228356932822259/114968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1631769149/100000000000000 : ℝ)*(base19) + (1773609161/100000000000000 : ℝ)*(base23) + (562504891/100000000000000 : ℝ)*(lower1) + (92796837/50000000000000 : ℝ)*(upper3) + (32175309/50000000000000 : ℝ)*(lower4) + (187382147/100000000000000 : ℝ)*(upper5) + (270030373203973/6250000000000 : ℝ)*(major0) + (270030373203973/6250000000000 : ℝ)*(major1) + (270030373203973/6250000000000 : ℝ)*(major2) + (614562707/25000000000000 : ℝ)*(sp2) + (5801049580938557/100000000000000 : ℝ)*(sp4) + (22660343551443/390625000000 : ℝ)*(sp5) + (5801045349078569/100000000000000 : ℝ)*(sp6) + (177495128555859/6250000000000 : ℝ)*(sp7) + (177495128555859/6250000000000 : ℝ)*(f.failure) + (5801049580938557/100000000000000 : ℝ)*(f.sum) + (2079007634731/1839500000000000000000000000 : ℝ)*base66 + (218241397108777997/229937500000000000000000000000000 : ℝ)*base67 + (2216604497304090497/229937500000000000000000000000000 : ℝ)*base69 + (2167170550803027997/229937500000000000000000000000000 : ℝ)*base71 + (6993639557/3592773437500000000000000 : ℝ)*base74 + (3366000157027972003/229937500000000000000000000000000 : ℝ)*base76 + (1100368579809340497/229937500000000000000000000000000 : ℝ)*base77 + (448859740284659503/229937500000000000000000000000000 : ℝ)*base80 + (920855668407/1839500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3460783/625000000000000000000 : ℝ)*base90 + (3460783/625000000000000000000 : ℝ)*base92 + (3460783/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1276_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1276_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1276_s8_0 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051200467/5000000000 : ℝ)*x 0 + (5416017031/10000000000 : ℝ)*x 1 + (5242431767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051200467/5000000000 : ℝ)^1059 ≤ (12787752402487/100000000000000 : ℝ)^803 := by
    have hnat : (1051200467 : ℕ)^1059*100000000000000^803 ≤ 12787752402487^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051200467 5000000000 12787752402487 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416017031/10000000000 : ℝ)^1059 ≤ (44542646615809/100000000000000 : ℝ)^803 := by
    have hnat : (5416017031 : ℕ)^1059*100000000000000^803 ≤ 44542646615809^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416017031 10000000000 44542646615809 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242431767/10000000000 : ℝ)^1059 ≤ (2133480048821/5000000000000 : ℝ)^803 := by
    have hnat : (5242431767 : ℕ)^1059*5000000000000^803 ≤ 2133480048821^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242431767 10000000000 2133480048821 5000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051200467/5000000000 : ℝ), (5416017031/10000000000 : ℝ), (5242431767/10000000000 : ℝ)] ![(12787752402487/100000000000000 : ℝ), (44542646615809/100000000000000 : ℝ), (2133480048821/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051200467/5000000000 : ℝ)|^1059 ≤ (12787752402487/100000000000000 : ℝ)^803
        have hw : |(-1051200467/5000000000 : ℝ)|=(1051200467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416017031/10000000000 : ℝ)|^1059 ≤ (44542646615809/100000000000000 : ℝ)^803
        have hw : |(5416017031/10000000000 : ℝ)|=(5416017031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242431767/10000000000 : ℝ)|^1059 ≤ (2133480048821/5000000000000 : ℝ)^803
        have hw : |(5242431767/10000000000 : ℝ)|=(5242431767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s8_1 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5350002447/10000000000 : ℝ)*x 0 + (-2190898881/10000000000 : ℝ)*x 1 + (5242431753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350002447/10000000000 : ℝ)^1059 ≤ (43828036217103/100000000000000 : ℝ)^803 := by
    have hnat : (5350002447 : ℕ)^1059*100000000000000^803 ≤ 43828036217103^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350002447 10000000000 43828036217103 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190898881/10000000000 : ℝ)^1059 ≤ (6751181467413/50000000000000 : ℝ)^803 := by
    have hnat : (2190898881 : ℕ)^1059*50000000000000^803 ≤ 6751181467413^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190898881 10000000000 6751181467413 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242431753/10000000000 : ℝ)^1059 ≤ (42669600826143/100000000000000 : ℝ)^803 := by
    have hnat : (5242431753 : ℕ)^1059*100000000000000^803 ≤ 42669600826143^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242431753 10000000000 42669600826143 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350002447/10000000000 : ℝ), (-2190898881/10000000000 : ℝ), (5242431753/10000000000 : ℝ)] ![(43828036217103/100000000000000 : ℝ), (6751181467413/50000000000000 : ℝ), (42669600826143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350002447/10000000000 : ℝ)|^1059 ≤ (43828036217103/100000000000000 : ℝ)^803
        have hw : |(5350002447/10000000000 : ℝ)|=(5350002447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190898881/10000000000 : ℝ)|^1059 ≤ (6751181467413/50000000000000 : ℝ)^803
        have hw : |(-2190898881/10000000000 : ℝ)|=(2190898881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242431753/10000000000 : ℝ)|^1059 ≤ (42669600826143/100000000000000 : ℝ)^803
        have hw : |(5242431753/10000000000 : ℝ)|=(5242431753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s8_2 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2675001231/5000000000 : ℝ)*x 0 + (5242431749/10000000000 : ℝ)*x 1 + (-2190898867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675001231/5000000000 : ℝ)^1059 ≤ (43828036379161/100000000000000 : ℝ)^803 := by
    have hnat : (2675001231 : ℕ)^1059*100000000000000^803 ≤ 43828036379161^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675001231 5000000000 43828036379161 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242431749/10000000000 : ℝ)^1059 ≤ (21334800391603/50000000000000 : ℝ)^803 := by
    have hnat : (5242431749 : ℕ)^1059*50000000000000^803 ≤ 21334800391603^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242431749 10000000000 21334800391603 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190898867/10000000000 : ℝ)^1059 ≤ (6751181410519/50000000000000 : ℝ)^803 := by
    have hnat : (2190898867 : ℕ)^1059*50000000000000^803 ≤ 6751181410519^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190898867 10000000000 6751181410519 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675001231/5000000000 : ℝ), (5242431749/10000000000 : ℝ), (-2190898867/10000000000 : ℝ)] ![(43828036379161/100000000000000 : ℝ), (21334800391603/50000000000000 : ℝ), (6751181410519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675001231/5000000000 : ℝ)|^1059 ≤ (43828036379161/100000000000000 : ℝ)^803
        have hw : |(2675001231/5000000000 : ℝ)|=(2675001231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242431749/10000000000 : ℝ)|^1059 ≤ (21334800391603/50000000000000 : ℝ)^803
        have hw : |(5242431749/10000000000 : ℝ)|=(5242431749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190898867/10000000000 : ℝ)|^1059 ≤ (6751181410519/50000000000000 : ℝ)^803
        have hw : |(-2190898867/10000000000 : ℝ)|=(2190898867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s8_3 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2172090723/5000000000 : ℝ)*x 0 + (417037533/1000000000 : ℝ)*x 1 + (1131238593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172090723/5000000000 : ℝ)^1059 ≤ (33302082285433/100000000000000 : ℝ)^803 := by
    have hnat : (2172090723 : ℕ)^1059*100000000000000^803 ≤ 33302082285433^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172090723 5000000000 33302082285433 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417037533/1000000000 : ℝ)^1059 ≤ (31556241826723/100000000000000 : ℝ)^803 := by
    have hnat : (417037533 : ℕ)^1059*100000000000000^803 ≤ 31556241826723^803*1000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417037533 1000000000 31556241826723 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131238593/2500000000 : ℝ)^1059 ≤ (35141675867777/100000000000000 : ℝ)^803 := by
    have hnat : (1131238593 : ℕ)^1059*100000000000000^803 ≤ 35141675867777^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131238593 2500000000 35141675867777 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172090723/5000000000 : ℝ), (417037533/1000000000 : ℝ), (1131238593/2500000000 : ℝ)] ![(33302082285433/100000000000000 : ℝ), (31556241826723/100000000000000 : ℝ), (35141675867777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172090723/5000000000 : ℝ)|^1059 ≤ (33302082285433/100000000000000 : ℝ)^803
        have hw : |(2172090723/5000000000 : ℝ)|=(2172090723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417037533/1000000000 : ℝ)|^1059 ≤ (31556241826723/100000000000000 : ℝ)^803
        have hw : |(417037533/1000000000 : ℝ)|=(417037533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131238593/2500000000 : ℝ)|^1059 ≤ (35141675867777/100000000000000 : ℝ)^803
        have hw : |(1131238593/2500000000 : ℝ)|=(1131238593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s8_4 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102413789/10000000000 : ℝ)*x 0 + (5243049467/10000000000 : ℝ)*x 1 + (2707698091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102413789/10000000000 : ℝ)^1059 ≤ (6393927759901/50000000000000 : ℝ)^803 := by
    have hnat : (2102413789 : ℕ)^1059*50000000000000^803 ≤ 6393927759901^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102413789 10000000000 6393927759901 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243049467/10000000000 : ℝ)^1059 ≤ (21338115781633/50000000000000 : ℝ)^803 := by
    have hnat : (5243049467 : ℕ)^1059*50000000000000^803 ≤ 21338115781633^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243049467 10000000000 21338115781633 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707698091/5000000000 : ℝ)^1059 ≤ (44535912904989/100000000000000 : ℝ)^803 := by
    have hnat : (2707698091 : ℕ)^1059*100000000000000^803 ≤ 44535912904989^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707698091 5000000000 44535912904989 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102413789/10000000000 : ℝ), (5243049467/10000000000 : ℝ), (2707698091/5000000000 : ℝ)] ![(6393927759901/50000000000000 : ℝ), (21338115781633/50000000000000 : ℝ), (44535912904989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102413789/10000000000 : ℝ)|^1059 ≤ (6393927759901/50000000000000 : ℝ)^803
        have hw : |(-2102413789/10000000000 : ℝ)|=(2102413789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243049467/10000000000 : ℝ)|^1059 ≤ (21338115781633/50000000000000 : ℝ)^803
        have hw : |(5243049467/10000000000 : ℝ)|=(5243049467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707698091/5000000000 : ℝ)|^1059 ≤ (44535912904989/100000000000000 : ℝ)^803
        have hw : |(2707698091/5000000000 : ℝ)|=(2707698091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s8_5 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305651379/10000000000 : ℝ)*x 0 + (-2017934479/10000000000 : ℝ)*x 1 + (5415396179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305651379/10000000000 : ℝ)^1059 ≤ (21674754208531/50000000000000 : ℝ)^803 := by
    have hnat : (5305651379 : ℕ)^1059*50000000000000^803 ≤ 21674754208531^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305651379 10000000000 21674754208531 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017934479/10000000000 : ℝ)^1059 ≤ (3028644675421/25000000000000 : ℝ)^803 := by
    have hnat : (2017934479 : ℕ)^1059*25000000000000^803 ≤ 3028644675421^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017934479 10000000000 3028644675421 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415396179/10000000000 : ℝ)^1059 ≤ (44535912872451/100000000000000 : ℝ)^803 := by
    have hnat : (5415396179 : ℕ)^1059*100000000000000^803 ≤ 44535912872451^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415396179 10000000000 44535912872451 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305651379/10000000000 : ℝ), (-2017934479/10000000000 : ℝ), (5415396179/10000000000 : ℝ)] ![(21674754208531/50000000000000 : ℝ), (3028644675421/25000000000000 : ℝ), (44535912872451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305651379/10000000000 : ℝ)|^1059 ≤ (21674754208531/50000000000000 : ℝ)^803
        have hw : |(5305651379/10000000000 : ℝ)|=(5305651379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2017934479/10000000000 : ℝ)|^1059 ≤ (3028644675421/25000000000000 : ℝ)^803
        have hw : |(-2017934479/10000000000 : ℝ)|=(2017934479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415396179/10000000000 : ℝ)|^1059 ≤ (44535912872451/100000000000000 : ℝ)^803
        have hw : |(5415396179/10000000000 : ℝ)|=(5415396179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s8_6 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530565139/1000000000 : ℝ)*x 0 + (2707698089/5000000000 : ℝ)*x 1 + (-403586893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530565139/1000000000 : ℝ)^1059 ≤ (43349508535589/100000000000000 : ℝ)^803 := by
    have hnat : (530565139 : ℕ)^1059*100000000000000^803 ≤ 43349508535589^803*1000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530565139 1000000000 43349508535589 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707698089/5000000000 : ℝ)^1059 ≤ (8907182572321/20000000000000 : ℝ)^803 := by
    have hnat : (2707698089 : ℕ)^1059*20000000000000^803 ≤ 8907182572321^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707698089 5000000000 8907182572321 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403586893/2000000000 : ℝ)^1059 ≤ (12114578590841/100000000000000 : ℝ)^803 := by
    have hnat : (403586893 : ℕ)^1059*100000000000000^803 ≤ 12114578590841^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403586893 2000000000 12114578590841 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530565139/1000000000 : ℝ), (2707698089/5000000000 : ℝ), (-403586893/2000000000 : ℝ)] ![(43349508535589/100000000000000 : ℝ), (8907182572321/20000000000000 : ℝ), (12114578590841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530565139/1000000000 : ℝ)|^1059 ≤ (43349508535589/100000000000000 : ℝ)^803
        have hw : |(530565139/1000000000 : ℝ)|=(530565139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707698089/5000000000 : ℝ)|^1059 ≤ (8907182572321/20000000000000 : ℝ)^803
        have hw : |(2707698089/5000000000 : ℝ)|=(2707698089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403586893/2000000000 : ℝ)|^1059 ≤ (12114578590841/100000000000000 : ℝ)^803
        have hw : |(-403586893/2000000000 : ℝ)|=(403586893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s8_7 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1086051939/2500000000 : ℝ)*x 0 + (4523692603/10000000000 : ℝ)*x 1 + (2085821791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086051939/2500000000 : ℝ)^1059 ≤ (16651174137657/50000000000000 : ℝ)^803 := by
    have hnat : (1086051939 : ℕ)^1059*50000000000000^803 ≤ 16651174137657^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086051939 2500000000 16651174137657 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523692603/10000000000 : ℝ)^1059 ≤ (17564376643927/50000000000000 : ℝ)^803 := by
    have hnat : (4523692603 : ℕ)^1059*50000000000000^803 ≤ 17564376643927^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523692603 10000000000 17564376643927 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085821791/5000000000 : ℝ)^1059 ≤ (31568898429619/100000000000000 : ℝ)^803 := by
    have hnat : (2085821791 : ℕ)^1059*100000000000000^803 ≤ 31568898429619^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085821791 5000000000 31568898429619 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086051939/2500000000 : ℝ), (4523692603/10000000000 : ℝ), (2085821791/5000000000 : ℝ)] ![(16651174137657/50000000000000 : ℝ), (17564376643927/50000000000000 : ℝ), (31568898429619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086051939/2500000000 : ℝ)|^1059 ≤ (16651174137657/50000000000000 : ℝ)^803
        have hw : |(1086051939/2500000000 : ℝ)|=(1086051939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523692603/10000000000 : ℝ)|^1059 ≤ (17564376643927/50000000000000 : ℝ)^803
        have hw : |(4523692603/10000000000 : ℝ)|=(4523692603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085821791/5000000000 : ℝ)|^1059 ≤ (31568898429619/100000000000000 : ℝ)^803
        have hw : |(2085821791/5000000000 : ℝ)|=(2085821791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1276_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (733/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5493/50000 : ℝ) ^ (4235/1024 : ℝ) ≤ (337294973210603/3125000000000000000 : ℝ) := by
    have hpowers : (5493/50000 : ℝ)^4235 ≤ (337294973210603/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5493 : ℕ)^4235*3125000000000000000^1024 ≤ 337294973210603^1024*50000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5493 50000 337294973210603 3125000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5493/50000 : ℝ)) (X := (337294973210603/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14661/100000 : ℝ) ^ (4235/1024 : ℝ) ≤ (35601442672734439/100000000000000000000 : ℝ) := by
    have hpowers : (14661/100000 : ℝ)^4235 ≤ (35601442672734439/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14661 : ℕ)^4235*100000000000000000000^1024 ≤ 35601442672734439^1024*100000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14661 100000 35601442672734439 100000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14661/100000 : ℝ)) (X := (35601442672734439/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562837294973210603/1562500000000000000 : ℝ) ≤ (19532269367741/19531250000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (1562837294973210603/1562500000000000000 : ℝ)^1024 ≤ (19532269367741/19531250000000 : ℝ)^4235 := by
      have hnat : (1562837294973210603 : ℕ)^1024*19531250000000^4235 ≤ 19532269367741^4235*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562837294973210603 1562500000000000000 19532269367741 19531250000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19532269367741/19531250000000 : ℝ)) (X := (1562837294973210603/1562500000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009278976363094747/20000000000000000000 : ℝ) ≤ (1250140200723961/1250000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (20009278976363094747/20000000000000000000 : ℝ)^1024 ≤ (1250140200723961/1250000000000000 : ℝ)^4235 := by
      have hnat : (20009278976363094747 : ℕ)^1024*1250000000000000^4235 ≤ 1250140200723961^4235*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009278976363094747 20000000000000000000 1250140200723961 1250000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250140200723961/1250000000000000 : ℝ)) (X := (20009278976363094747/20000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035601442672734439/50000000000000000000 : ℝ) ≤ (625107580956249/625000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (50035601442672734439/50000000000000000000 : ℝ)^1024 ≤ (625107580956249/625000000000000 : ℝ)^4235 := by
      have hnat : (50035601442672734439 : ℕ)^1024*625000000000000^4235 ≤ 625107580956249^4235*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035601442672734439 50000000000000000000 625107580956249 625000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625107580956249/625000000000000 : ℝ)) (X := (50035601442672734439/50000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(337294973210603/3125000000000000000 : ℝ) ≤ ((382695225671512353/382812500000000000 : ℝ)+2*(74961188537/45937500000000 : ℝ)*(5493/50000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (382695225671512353/382812500000000000 : ℝ)+2*(74961188537/45937500000000 : ℝ)*(5493/50000 : ℝ)=(19532269367741/19531250000000 : ℝ) by norm_num, show 1+2*(337294973210603/3125000000000000000 : ℝ)=(1562837294973210603/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35601442672734439/100000000000000000000 : ℝ)+(337294973210603/3125000000000000000 : ℝ) ≤ ((382695225671512353/382812500000000000 : ℝ)+(74961188537/45937500000000 : ℝ)*((14661/100000 : ℝ)+(5493/50000 : ℝ)))^(4235/1024 : ℝ) := by
    rw [show (382695225671512353/382812500000000000 : ℝ)+(74961188537/45937500000000 : ℝ)*((14661/100000 : ℝ)+(5493/50000 : ℝ))=(1250140200723961/1250000000000000 : ℝ) by norm_num, show 1+(35601442672734439/100000000000000000000 : ℝ)+(337294973210603/3125000000000000000 : ℝ)=(20009278976363094747/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35601442672734439/100000000000000000000 : ℝ) ≤ ((382695225671512353/382812500000000000 : ℝ)+2*(74961188537/45937500000000 : ℝ)*(14661/100000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (382695225671512353/382812500000000000 : ℝ)+2*(74961188537/45937500000000 : ℝ)*(14661/100000 : ℝ)=(625107580956249/625000000000000 : ℝ) by norm_num, show 1+2*(35601442672734439/100000000000000000000 : ℝ)=(50035601442672734439/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (382695225671512353/382812500000000000 : ℝ)*(X 1 0+X 2 0)+(74961188537/45937500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (382695225671512353/382812500000000000 : ℝ)) (alpha := (74961188537/45937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (382695225671512353/382812500000000000 : ℝ)*(X 0 1+X 2 1)+(74961188537/45937500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (382695225671512353/382812500000000000 : ℝ)) (alpha := (74961188537/45937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (382695225671512353/382812500000000000 : ℝ)*(X 0 2+X 1 2)+(74961188537/45937500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (14661/100000 : ℝ)) (c := (382695225671512353/382812500000000000 : ℝ)) (alpha := (74961188537/45937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1051200467/5000000000 : ℝ)*X 0 0+(5416017031/10000000000 : ℝ)*X 0 1+(5242431767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350002447/10000000000 : ℝ)*X 1 0+(-2190898881/10000000000 : ℝ)*X 1 1+(5242431753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675001231/5000000000 : ℝ)*X 2 0+(5242431749/10000000000 : ℝ)*X 2 1+(-2190898867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2172090723/5000000000 : ℝ)*X 0 0+(417037533/1000000000 : ℝ)*X 0 1+(1131238593/2500000000 : ℝ)*X 0 2+(2172090723/5000000000 : ℝ)*X 1 0+(417037533/1000000000 : ℝ)*X 1 1+(1131238593/2500000000 : ℝ)*X 1 2+(2172090723/5000000000 : ℝ)*X 2 0+(417037533/1000000000 : ℝ)*X 2 1+(1131238593/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2102413789/10000000000 : ℝ)*X 0 0+(5243049467/10000000000 : ℝ)*X 0 1+(2707698091/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305651379/10000000000 : ℝ)*X 1 0+(-2017934479/10000000000 : ℝ)*X 1 1+(5415396179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530565139/1000000000 : ℝ)*X 2 0+(2707698089/5000000000 : ℝ)*X 2 1+(-403586893/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086051939/2500000000 : ℝ)*X 0 0+(4523692603/10000000000 : ℝ)*X 0 1+(2085821791/5000000000 : ℝ)*X 0 2+(1086051939/2500000000 : ℝ)*X 1 0+(4523692603/10000000000 : ℝ)*X 1 1+(2085821791/5000000000 : ℝ)*X 1 2+(1086051939/2500000000 : ℝ)*X 2 0+(4523692603/10000000000 : ℝ)*X 2 1+(2085821791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (224957457062894967115783/48828125000000000000000000000 : ℝ) := by norm_num
    linear_combination (96505453/10000000000000 : ℝ)*(base19) + (935257557/100000000000000 : ℝ)*(base23) + (24582731/100000000000000 : ℝ)*(lower2) + (1736077/1562500000000 : ℝ)*(upper3) + (96762881/100000000000000 : ℝ)*(upper5) + (1072645237108663/25000000000000 : ℝ)*(major0) + (1072645237108663/25000000000000 : ℝ)*(major1) + (1072645237108663/25000000000000 : ℝ)*(major2) + (720109633043203/12500000000000 : ℝ)*(sp0) + (5760895754033103/100000000000000 : ℝ)*(sp1) + (1440223945957519/25000000000000 : ℝ)*(sp2) + (352531884567799/12500000000000 : ℝ)*(sp3) + (1965474201/10000000000000 : ℝ)*(sp4) + (9947668311/100000000000000 : ℝ)*(sp7) + (176266564013169/6250000000000 : ℝ)*(f.failure) + (5760896719087633/100000000000000 : ℝ)*(f.sum) + (11404745161879/9187500000000000000000000000 : ℝ)*base66 + (267824440423831391/57421875000000000000000000000000 : ℝ)*base68 + (95237344115918377/7177734375000000000000000000000 : ℝ)*base70 + (341448361538675141/57421875000000000000000000000000 : ℝ)*base72 + (67588967245871/9187500000000000000000000000 : ℝ)*base73 + (503860702637112641/57421875000000000000000000000000 : ℝ)*base76 + (320613766401564133/28710937500000000000000000000000 : ℝ)*base78 + (350255899119137359/57421875000000000000000000000000 : ℝ)*base79 + (30120424042871/9187500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9158747/625000000000000000000 : ℝ)*base89 + (9158747/625000000000000000000 : ℝ)*base91 + (9158747/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60964003122395008361724501/19140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136148233/25000000000000 : ℝ)*(base19) + (15571081/2500000000000 : ℝ)*(base23) + (93853593/50000000000000 : ℝ)*(lower1) + (30113211/50000000000000 : ℝ)*(upper3) + (5829819/20000000000000 : ℝ)*(lower4) + (71149287/100000000000000 : ℝ)*(upper5) + (4321377211998839/100000000000000 : ℝ)*(major0) + (4321377211998839/100000000000000 : ℝ)*(major1) + (4321377211998839/100000000000000 : ℝ)*(major2) + (269906409/20000000000000 : ℝ)*(sp2) + (5802246434655841/100000000000000 : ℝ)*(sp4) + (5802245890062909/100000000000000 : ℝ)*(sp5) + (5802244462280557/100000000000000 : ℝ)*(sp6) + (1420253941586613/50000000000000 : ℝ)*(sp7) + (1420253941586613/50000000000000 : ℝ)*(f.failure) + (5802246434655841/100000000000000 : ℝ)*(f.sum) + (57378289352219/18375000000000000000000000000 : ℝ)*base65 + (581485327660455751/114843750000000000000000000000000 : ℝ)*base67 + (929364659560637999/114843750000000000000000000000000 : ℝ)*base70 + (514102036616106749/114843750000000000000000000000000 : ℝ)*base72 + (50381850812219/18375000000000000000000000000 : ℝ)*base73 + (2954384480187981749/114843750000000000000000000000000 : ℝ)*base76 + (236446313040325499/114843750000000000000000000000000 : ℝ)*base78 + (499857122955751/114843750000000000000000000000000 : ℝ)*base79 + (793092684833/574218750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6562681/5000000000000000000000 : ℝ)*base90 + (6562681/5000000000000000000000 : ℝ)*base92 + (6562681/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1276_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (733/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1276_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1276_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10971/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (733/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1276_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1276_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1276_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10971/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (733/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1276_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
