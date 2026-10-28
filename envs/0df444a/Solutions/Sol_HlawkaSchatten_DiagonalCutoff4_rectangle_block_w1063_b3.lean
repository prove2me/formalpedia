-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1063_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:04:55.5355+00:00
-- url     : https://prove2.me/submissions/f61a21c1-64fd-4bc5-aeb4-70754bafb704

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
theorem support_rectangle_w1063_s9_0 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102624779/5000000000 : ℝ)*x 0 + (5394383993/10000000000 : ℝ)*x 1 + (2632210371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102624779/5000000000 : ℝ)^129 ≤ (2678529781973/20000000000000 : ℝ)^97 := by
    have hnat : (1102624779 : ℕ)^129*20000000000000^97 ≤ 2678529781973^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102624779 5000000000 2678529781973 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394383993/10000000000 : ℝ)^129 ≤ (8801167809003/20000000000000 : ℝ)^97 := by
    have hnat : (5394383993 : ℕ)^129*20000000000000^97 ≤ 8801167809003^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394383993 10000000000 8801167809003 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632210371/5000000000 : ℝ)^129 ≤ (5325189004103/12500000000000 : ℝ)^97 := by
    have hnat : (2632210371 : ℕ)^129*12500000000000^97 ≤ 5325189004103^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632210371 5000000000 5325189004103 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102624779/5000000000 : ℝ), (5394383993/10000000000 : ℝ), (2632210371/5000000000 : ℝ)] ![(2678529781973/20000000000000 : ℝ), (8801167809003/20000000000000 : ℝ), (5325189004103/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102624779/5000000000 : ℝ)|^129 ≤ (2678529781973/20000000000000 : ℝ)^97
        have hw : |(-1102624779/5000000000 : ℝ)|=(1102624779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394383993/10000000000 : ℝ)|^129 ≤ (8801167809003/20000000000000 : ℝ)^97
        have hw : |(5394383993/10000000000 : ℝ)|=(5394383993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632210371/5000000000 : ℝ)|^129 ≤ (5325189004103/12500000000000 : ℝ)^97
        have hw : |(2632210371/5000000000 : ℝ)|=(2632210371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s9_1 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (267248951/500000000 : ℝ)*x 0 + (-1135594637/5000000000 : ℝ)*x 1 + (105288421/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267248951/500000000 : ℝ)^129 ≤ (43470659928891/100000000000000 : ℝ)^97 := by
    have hnat : (267248951 : ℕ)^129*100000000000000^97 ≤ 43470659928891^97*500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267248951 500000000 43470659928891 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135594637/5000000000 : ℝ)^129 ≤ (696391235923/5000000000000 : ℝ)^97 := by
    have hnat : (1135594637 : ℕ)^129*5000000000000^97 ≤ 696391235923^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135594637 5000000000 696391235923 5000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105288421/200000000 : ℝ)^129 ≤ (8520303069503/20000000000000 : ℝ)^97 := by
    have hnat : (105288421 : ℕ)^129*20000000000000^97 ≤ 8520303069503^97*200000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105288421 200000000 8520303069503 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267248951/500000000 : ℝ), (-1135594637/5000000000 : ℝ), (105288421/200000000 : ℝ)] ![(43470659928891/100000000000000 : ℝ), (696391235923/5000000000000 : ℝ), (8520303069503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267248951/500000000 : ℝ)|^129 ≤ (43470659928891/100000000000000 : ℝ)^97
        have hw : |(267248951/500000000 : ℝ)|=(267248951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135594637/5000000000 : ℝ)|^129 ≤ (696391235923/5000000000000 : ℝ)^97
        have hw : |(-1135594637/5000000000 : ℝ)|=(1135594637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105288421/200000000 : ℝ)|^129 ≤ (8520303069503/20000000000000 : ℝ)^97
        have hw : |(105288421/200000000 : ℝ)|=(105288421/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s9_2 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5344979473/10000000000 : ℝ)*x 0 + (1316105177/2500000000 : ℝ)*x 1 + (-2271189123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344979473/10000000000 : ℝ)^129 ≤ (10867666207139/25000000000000 : ℝ)^97 := by
    have hnat : (5344979473 : ℕ)^129*25000000000000^97 ≤ 10867666207139^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344979473 10000000000 10867666207139 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316105177/2500000000 : ℝ)^129 ≤ (10650377916729/25000000000000 : ℝ)^97 := by
    have hnat : (1316105177 : ℕ)^129*25000000000000^97 ≤ 10650377916729^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316105177 2500000000 10650377916729 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271189123/10000000000 : ℝ)^129 ≤ (13927823486987/100000000000000 : ℝ)^97 := by
    have hnat : (2271189123 : ℕ)^129*100000000000000^97 ≤ 13927823486987^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271189123 10000000000 13927823486987 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344979473/10000000000 : ℝ), (1316105177/2500000000 : ℝ), (-2271189123/10000000000 : ℝ)] ![(10867666207139/25000000000000 : ℝ), (10650377916729/25000000000000 : ℝ), (13927823486987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344979473/10000000000 : ℝ)|^129 ≤ (10867666207139/25000000000000 : ℝ)^97
        have hw : |(5344979473/10000000000 : ℝ)|=(5344979473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316105177/2500000000 : ℝ)|^129 ≤ (10650377916729/25000000000000 : ℝ)^97
        have hw : |(1316105177/2500000000 : ℝ)|=(1316105177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2271189123/10000000000 : ℝ)|^129 ≤ (13927823486987/100000000000000 : ℝ)^97
        have hw : |(-2271189123/10000000000 : ℝ)|=(2271189123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s9_3 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4375925187/10000000000 : ℝ)*x 0 + (42505231/100000000 : ℝ)*x 1 + (4505080211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375925187/10000000000 : ℝ)^129 ≤ (33316544770671/100000000000000 : ℝ)^97 := by
    have hnat : (4375925187 : ℕ)^129*100000000000000^97 ≤ 33316544770671^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375925187 10000000000 33316544770671 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42505231/100000000 : ℝ)^129 ≤ (1282114059503/4000000000000 : ℝ)^97 := by
    have hnat : (42505231 : ℕ)^129*4000000000000^97 ≤ 1282114059503^97*100000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42505231 100000000 1282114059503 4000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505080211/10000000000 : ℝ)^129 ≤ (8657650930523/25000000000000 : ℝ)^97 := by
    have hnat : (4505080211 : ℕ)^129*25000000000000^97 ≤ 8657650930523^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505080211 10000000000 8657650930523 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375925187/10000000000 : ℝ), (42505231/100000000 : ℝ), (4505080211/10000000000 : ℝ)] ![(33316544770671/100000000000000 : ℝ), (1282114059503/4000000000000 : ℝ), (8657650930523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375925187/10000000000 : ℝ)|^129 ≤ (33316544770671/100000000000000 : ℝ)^97
        have hw : |(4375925187/10000000000 : ℝ)|=(4375925187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42505231/100000000 : ℝ)|^129 ≤ (1282114059503/4000000000000 : ℝ)^97
        have hw : |(42505231/100000000 : ℝ)|=(42505231/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505080211/10000000000 : ℝ)|^129 ≤ (8657650930523/25000000000000 : ℝ)^97
        have hw : |(4505080211/10000000000 : ℝ)|=(4505080211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s9_4 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102627343/5000000000 : ℝ)*x 0 + (2632373211/5000000000 : ℝ)*x 1 + (5394057099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102627343/5000000000 : ℝ)^129 ≤ (13392690326509/100000000000000 : ℝ)^97 := by
    have hnat : (1102627343 : ℕ)^129*100000000000000^97 ≤ 13392690326509^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102627343 5000000000 13392690326509 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632373211/5000000000 : ℝ)^129 ≤ (4260501703199/10000000000000 : ℝ)^97 := by
    have hnat : (2632373211 : ℕ)^129*10000000000000^97 ≤ 4260501703199^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632373211 5000000000 4260501703199 10000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394057099/10000000000 : ℝ)^129 ≤ (8800458526857/20000000000000 : ℝ)^97 := by
    have hnat : (5394057099 : ℕ)^129*20000000000000^97 ≤ 8800458526857^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394057099 10000000000 8800458526857 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102627343/5000000000 : ℝ), (2632373211/5000000000 : ℝ), (5394057099/10000000000 : ℝ)] ![(13392690326509/100000000000000 : ℝ), (4260501703199/10000000000000 : ℝ), (8800458526857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102627343/5000000000 : ℝ)|^129 ≤ (13392690326509/100000000000000 : ℝ)^97
        have hw : |(-1102627343/5000000000 : ℝ)|=(1102627343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632373211/5000000000 : ℝ)|^129 ≤ (4260501703199/10000000000000 : ℝ)^97
        have hw : |(2632373211/5000000000 : ℝ)|=(2632373211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394057099/10000000000 : ℝ)|^129 ≤ (8800458526857/20000000000000 : ℝ)^97
        have hw : |(5394057099/10000000000 : ℝ)|=(5394057099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s9_5 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312251617/10000000000 : ℝ)*x 0 + (-214155307/1000000000 : ℝ)*x 1 + (539405739/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312251617/10000000000 : ℝ)^129 ≤ (43117037098993/100000000000000 : ℝ)^97 := by
    have hnat : (5312251617 : ℕ)^129*100000000000000^97 ≤ 43117037098993^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312251617 10000000000 43117037098993 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214155307/1000000000 : ℝ)^129 ≤ (6440333545501/50000000000000 : ℝ)^97 := by
    have hnat : (214155307 : ℕ)^129*50000000000000^97 ≤ 6440333545501^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214155307 1000000000 6440333545501 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539405739/1000000000 : ℝ)^129 ≤ (44002295791257/100000000000000 : ℝ)^97 := by
    have hnat : (539405739 : ℕ)^129*100000000000000^97 ≤ 44002295791257^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539405739 1000000000 44002295791257 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312251617/10000000000 : ℝ), (-214155307/1000000000 : ℝ), (539405739/1000000000 : ℝ)] ![(43117037098993/100000000000000 : ℝ), (6440333545501/50000000000000 : ℝ), (44002295791257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312251617/10000000000 : ℝ)|^129 ≤ (43117037098993/100000000000000 : ℝ)^97
        have hw : |(5312251617/10000000000 : ℝ)|=(5312251617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214155307/1000000000 : ℝ)|^129 ≤ (6440333545501/50000000000000 : ℝ)^97
        have hw : |(-214155307/1000000000 : ℝ)|=(214155307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539405739/1000000000 : ℝ)|^129 ≤ (44002295791257/100000000000000 : ℝ)^97
        have hw : |(539405739/1000000000 : ℝ)|=(539405739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s9_6 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4375933741/10000000000 : ℝ)*x 0 + (4504443853/10000000000 : ℝ)*x 1 + (4251163119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375933741/10000000000 : ℝ)^129 ≤ (2082289461409/6250000000000 : ℝ)^97 := by
    have hnat : (4375933741 : ℕ)^129*6250000000000^97 ≤ 2082289461409^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375933741 10000000000 2082289461409 6250000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504443853/10000000000 : ℝ)^129 ≤ (1384963937141/4000000000000 : ℝ)^97 := by
    have hnat : (4504443853 : ℕ)^129*4000000000000^97 ≤ 1384963937141^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504443853 10000000000 1384963937141 4000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251163119/10000000000 : ℝ)^129 ≤ (6411854034091/20000000000000 : ℝ)^97 := by
    have hnat : (4251163119 : ℕ)^129*20000000000000^97 ≤ 6411854034091^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251163119 10000000000 6411854034091 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375933741/10000000000 : ℝ), (4504443853/10000000000 : ℝ), (4251163119/10000000000 : ℝ)] ![(2082289461409/6250000000000 : ℝ), (1384963937141/4000000000000 : ℝ), (6411854034091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375933741/10000000000 : ℝ)|^129 ≤ (2082289461409/6250000000000 : ℝ)^97
        have hw : |(4375933741/10000000000 : ℝ)|=(4375933741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504443853/10000000000 : ℝ)|^129 ≤ (1384963937141/4000000000000 : ℝ)^97
        have hw : |(4504443853/10000000000 : ℝ)|=(4504443853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251163119/10000000000 : ℝ)|^129 ≤ (6411854034091/20000000000000 : ℝ)^97
        have hw : |(4251163119/10000000000 : ℝ)|=(4251163119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1063_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (703/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11247/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11247/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11247/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11247/100000 : ℝ) ^ (8255/2048 : ℝ) ≤ (467525237980497/3125000000000000000 : ℝ) := by
    have hpowers : (11247/100000 : ℝ)^8255 ≤ (467525237980497/3125000000000000000 : ℝ)^2048 := by
      have hnat : (11247 : ℕ)^8255*3125000000000000000^2048 ≤ 467525237980497^2048*100000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11247 100000 467525237980497 3125000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11247/100000 : ℝ)) (X := (467525237980497/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14001/100000 : ℝ) ^ (8255/2048 : ℝ) ≤ (36171840523481333/100000000000000000000 : ℝ) := by
    have hpowers : (14001/100000 : ℝ)^8255 ≤ (36171840523481333/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14001 : ℕ)^8255*100000000000000000000^2048 ≤ 36171840523481333^2048*100000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14001 100000 36171840523481333 100000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14001/100000 : ℝ)) (X := (36171840523481333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562967525237980497/1562500000000000000 : ℝ) ≤ (2500185562010229/2500000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (1562967525237980497/1562500000000000000 : ℝ)^2048 ≤ (2500185562010229/2500000000000000 : ℝ)^8255 := by
      have hnat : (1562967525237980497 : ℕ)^2048*2500000000000000^8255 ≤ 2500185562010229^8255*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562967525237980497 1562500000000000000 2500185562010229 2500000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185562010229/2500000000000000 : ℝ)) (X := (1562967525237980497/1562500000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051132648138857237/100000000000000000000 : ℝ) ≤ (1000126831663949/1000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (100051132648138857237/100000000000000000000 : ℝ)^2048 ≤ (1000126831663949/1000000000000000 : ℝ)^8255 := by
      have hnat : (100051132648138857237 : ℕ)^2048*1000000000000000^8255 ≤ 1000126831663949^8255*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051132648138857237 100000000000000000000 1000126831663949 1000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000126831663949/1000000000000000 : ℝ)) (X := (100051132648138857237/100000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036171840523481333/50000000000000000000 : ℝ) ≤ (625112149077379/625000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50036171840523481333/50000000000000000000 : ℝ)^2048 ≤ (625112149077379/625000000000000 : ℝ)^8255 := by
      have hnat : (50036171840523481333 : ℕ)^2048*625000000000000^8255 ≤ 625112149077379^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036171840523481333 50000000000000000000 625112149077379 625000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625112149077379/625000000000000 : ℝ)) (X := (50036171840523481333/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(467525237980497/3125000000000000000 : ℝ) ≤ ((2294184230337363259/2295000000000000000 : ℝ)+2*(263034299287/137700000000000 : ℝ)*(11247/100000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (2294184230337363259/2295000000000000000 : ℝ)+2*(263034299287/137700000000000 : ℝ)*(11247/100000 : ℝ)=(2500185562010229/2500000000000000 : ℝ) by norm_num, show 1+2*(467525237980497/3125000000000000000 : ℝ)=(1562967525237980497/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36171840523481333/100000000000000000000 : ℝ)+(467525237980497/3125000000000000000 : ℝ) ≤ ((2294184230337363259/2295000000000000000 : ℝ)+(263034299287/137700000000000 : ℝ)*((14001/100000 : ℝ)+(11247/100000 : ℝ)))^(8255/2048 : ℝ) := by
    rw [show (2294184230337363259/2295000000000000000 : ℝ)+(263034299287/137700000000000 : ℝ)*((14001/100000 : ℝ)+(11247/100000 : ℝ))=(1000126831663949/1000000000000000 : ℝ) by norm_num, show 1+(36171840523481333/100000000000000000000 : ℝ)+(467525237980497/3125000000000000000 : ℝ)=(100051132648138857237/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36171840523481333/100000000000000000000 : ℝ) ≤ ((2294184230337363259/2295000000000000000 : ℝ)+2*(263034299287/137700000000000 : ℝ)*(14001/100000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (2294184230337363259/2295000000000000000 : ℝ)+2*(263034299287/137700000000000 : ℝ)*(14001/100000 : ℝ)=(625112149077379/625000000000000 : ℝ) by norm_num, show 1+2*(36171840523481333/100000000000000000000 : ℝ)=(50036171840523481333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2294184230337363259/2295000000000000000 : ℝ)*(X 1 0+X 2 0)+(263034299287/137700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (2294184230337363259/2295000000000000000 : ℝ)) (alpha := (263034299287/137700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2294184230337363259/2295000000000000000 : ℝ)*(X 0 1+X 2 1)+(263034299287/137700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (2294184230337363259/2295000000000000000 : ℝ)) (alpha := (263034299287/137700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2294184230337363259/2295000000000000000 : ℝ)*(X 0 2+X 1 2)+(263034299287/137700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (11247/100000 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (2294184230337363259/2295000000000000000 : ℝ)) (alpha := (263034299287/137700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1102624779/5000000000 : ℝ)*X 0 0+(5394383993/10000000000 : ℝ)*X 0 1+(2632210371/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267248951/500000000 : ℝ)*X 1 0+(-1135594637/5000000000 : ℝ)*X 1 1+(105288421/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344979473/10000000000 : ℝ)*X 2 0+(1316105177/2500000000 : ℝ)*X 2 1+(-2271189123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375925187/10000000000 : ℝ)*X 0 0+(42505231/100000000 : ℝ)*X 0 1+(4505080211/10000000000 : ℝ)*X 0 2+(4375925187/10000000000 : ℝ)*X 1 0+(42505231/100000000 : ℝ)*X 1 1+(4505080211/10000000000 : ℝ)*X 1 2+(4375925187/10000000000 : ℝ)*X 2 0+(42505231/100000000 : ℝ)*X 2 1+(4505080211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1102627343/5000000000 : ℝ)*X 0 0+(2632373211/5000000000 : ℝ)*X 0 1+(5394057099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312251617/10000000000 : ℝ)*X 1 0+(-214155307/1000000000 : ℝ)*X 1 1+(539405739/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4375933741/10000000000 : ℝ)*X 0 0+(4504443853/10000000000 : ℝ)*X 0 1+(4251163119/10000000000 : ℝ)*X 0 2+(4375933741/10000000000 : ℝ)*X 1 0+(4504443853/10000000000 : ℝ)*X 1 1+(4251163119/10000000000 : ℝ)*X 1 2+(4375933741/10000000000 : ℝ)*X 2 0+(4504443853/10000000000 : ℝ)*X 2 1+(4251163119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1691387438556747829181/382500000000000000000000000 : ℝ) := by norm_num
    linear_combination (115914763/25000000000000 : ℝ)*(base19) + (521970393/50000000000000 : ℝ)*(base23) + (22811251/50000000000000 : ℝ)*(lower2) + (241354347/100000000000000 : ℝ)*(upper5) + (2905735164478267/50000000000000 : ℝ)*(major0) + (2905735164478267/50000000000000 : ℝ)*(major1) + (2905735164478267/50000000000000 : ℝ)*(major2) + (961812520677667/12500000000000 : ℝ)*(sp0) + (1923633730091649/25000000000000 : ℝ)*(sp1) + (3847268272996719/50000000000000 : ℝ)*(sp2) + (785679529211523/20000000000000 : ℝ)*(sp3) + (37424512889/100000000000000 : ℝ)*(sp4) + (2205908577/100000000000000 : ℝ)*(sp5) + (263726181/5000000000000 : ℝ)*(sp6) + (982100730145309/25000000000000 : ℝ)*(f.failure) + (480908599370889/6250000000000 : ℝ)*(f.sum) + (32591961429803/6885000000000000000000000000 : ℝ)*base65 + (533692178294673541/344250000000000000000000000000000 : ℝ)*base68 + (407347658791826459/344250000000000000000000000000000 : ℝ)*base69 + (2885562619986326459/344250000000000000000000000000000 : ℝ)*base71 + (81120738803/430312500000000000000000000 : ℝ)*base73 + (8266127311492923541/344250000000000000000000000000000 : ℝ)*base76 + (4589096397895076459/344250000000000000000000000000000 : ℝ)*base77 + (2242757896381173541/344250000000000000000000000000000 : ℝ)*base80 + (3901763051423/6885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (20561429/2500000000000000000000 : ℝ)*base89 + (20561429/2500000000000000000000 : ℝ)*base91 + (20561429/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1063_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1063_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1063_box_0 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-415135413/2000000000 : ℝ)*x 0 + (672176283/1250000000 : ℝ)*x 1 + (5377409957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415135413/2000000000 : ℝ)^129 ≤ (3089106781161/25000000000000 : ℝ)^97 := by
    have hnat : (415135413 : ℕ)^129*25000000000000^97 ≤ 3089106781161^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415135413 2000000000 3089106781161 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672176283/1250000000 : ℝ)^129 ≤ (10955447023747/25000000000000 : ℝ)^97 := by
    have hnat : (672176283 : ℕ)^129*25000000000000^97 ≤ 10955447023747^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672176283 1250000000 10955447023747 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377409957/10000000000 : ℝ)^129 ≤ (43821784767831/100000000000000 : ℝ)^97 := by
    have hnat : (5377409957 : ℕ)^129*100000000000000^97 ≤ 43821784767831^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377409957 10000000000 43821784767831 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415135413/2000000000 : ℝ), (672176283/1250000000 : ℝ), (5377409957/10000000000 : ℝ)] ![(3089106781161/25000000000000 : ℝ), (10955447023747/25000000000000 : ℝ), (43821784767831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415135413/2000000000 : ℝ)|^129 ≤ (3089106781161/25000000000000 : ℝ)^97
        have hw : |(-415135413/2000000000 : ℝ)|=(415135413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672176283/1250000000 : ℝ)|^129 ≤ (10955447023747/25000000000000 : ℝ)^97
        have hw : |(672176283/1250000000 : ℝ)|=(672176283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377409957/10000000000 : ℝ)|^129 ≤ (43821784767831/100000000000000 : ℝ)^97
        have hw : |(5377409957/10000000000 : ℝ)|=(5377409957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_1 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5295169191/10000000000 : ℝ)*x 0 + (-546750347/2500000000 : ℝ)*x 1 + (537741019/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295169191/10000000000 : ℝ)^129 ≤ (21466372395019/50000000000000 : ℝ)^97 := by
    have hnat : (5295169191 : ℕ)^129*50000000000000^97 ≤ 21466372395019^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295169191 10000000000 21466372395019 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546750347/2500000000 : ℝ)^129 ≤ (13245467910423/100000000000000 : ℝ)^97 := by
    have hnat : (546750347 : ℕ)^129*100000000000000^97 ≤ 13245467910423^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546750347 2500000000 13245467910423 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537741019/1000000000 : ℝ)^129 ≤ (21910893646501/50000000000000 : ℝ)^97 := by
    have hnat : (537741019 : ℕ)^129*50000000000000^97 ≤ 21910893646501^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537741019 1000000000 21910893646501 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295169191/10000000000 : ℝ), (-546750347/2500000000 : ℝ), (537741019/1000000000 : ℝ)] ![(21466372395019/50000000000000 : ℝ), (13245467910423/100000000000000 : ℝ), (21910893646501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295169191/10000000000 : ℝ)|^129 ≤ (21466372395019/50000000000000 : ℝ)^97
        have hw : |(5295169191/10000000000 : ℝ)|=(5295169191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-546750347/2500000000 : ℝ)|^129 ≤ (13245467910423/100000000000000 : ℝ)^97
        have hw : |(-546750347/2500000000 : ℝ)|=(546750347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537741019/1000000000 : ℝ)|^129 ≤ (21910893646501/50000000000000 : ℝ)^97
        have hw : |(537741019/1000000000 : ℝ)|=(537741019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_2 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (82737019/156250000 : ℝ)*x 0 + (2688705021/5000000000 : ℝ)*x 1 + (-1093500777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82737019/156250000 : ℝ)^129 ≤ (8586549011921/20000000000000 : ℝ)^97 := by
    have hnat : (82737019 : ℕ)^129*20000000000000^97 ≤ 8586549011921^97*156250000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82737019 156250000 8586549011921 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688705021/5000000000 : ℝ)^129 ≤ (43821785689031/100000000000000 : ℝ)^97 := by
    have hnat : (2688705021 : ℕ)^129*100000000000000^97 ≤ 43821785689031^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688705021 5000000000 43821785689031 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093500777/5000000000 : ℝ)^129 ≤ (13245469247463/100000000000000 : ℝ)^97 := by
    have hnat : (1093500777 : ℕ)^129*100000000000000^97 ≤ 13245469247463^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093500777 5000000000 13245469247463 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82737019/156250000 : ℝ), (2688705021/5000000000 : ℝ), (-1093500777/5000000000 : ℝ)] ![(8586549011921/20000000000000 : ℝ), (43821785689031/100000000000000 : ℝ), (13245469247463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82737019/156250000 : ℝ)|^129 ≤ (8586549011921/20000000000000 : ℝ)^97
        have hw : |(82737019/156250000 : ℝ)|=(82737019/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688705021/5000000000 : ℝ)|^129 ≤ (43821785689031/100000000000000 : ℝ)^97
        have hw : |(2688705021/5000000000 : ℝ)|=(2688705021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093500777/5000000000 : ℝ)|^129 ≤ (13245469247463/100000000000000 : ℝ)^97
        have hw : |(-1093500777/5000000000 : ℝ)|=(1093500777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_3 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2242174473/5000000000 : ℝ)*x 0 + (2161938881/5000000000 : ℝ)*x 1 + (4323877623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242174473/5000000000 : ℝ)^129 ≤ (34418830425551/100000000000000 : ℝ)^97 := by
    have hnat : (2242174473 : ℕ)^129*100000000000000^97 ≤ 34418830425551^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242174473 5000000000 34418830425551 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161938881/5000000000 : ℝ)^129 ≤ (32790585480941/100000000000000 : ℝ)^97 := by
    have hnat : (2161938881 : ℕ)^129*100000000000000^97 ≤ 32790585480941^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161938881 5000000000 32790585480941 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4323877623/10000000000 : ℝ)^129 ≤ (8197646019767/25000000000000 : ℝ)^97 := by
    have hnat : (4323877623 : ℕ)^129*25000000000000^97 ≤ 8197646019767^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323877623 10000000000 8197646019767 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242174473/5000000000 : ℝ), (2161938881/5000000000 : ℝ), (4323877623/10000000000 : ℝ)] ![(34418830425551/100000000000000 : ℝ), (32790585480941/100000000000000 : ℝ), (8197646019767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242174473/5000000000 : ℝ)|^129 ≤ (34418830425551/100000000000000 : ℝ)^97
        have hw : |(2242174473/5000000000 : ℝ)|=(2242174473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2161938881/5000000000 : ℝ)|^129 ≤ (32790585480941/100000000000000 : ℝ)^97
        have hw : |(2161938881/5000000000 : ℝ)|=(2161938881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4323877623/10000000000 : ℝ)|^129 ≤ (8197646019767/25000000000000 : ℝ)^97
        have hw : |(4323877623/10000000000 : ℝ)|=(4323877623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_4 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-116810081/500000000 : ℝ)*x 0 + (1056008987/2000000000 : ℝ)*x 1 + (1320011221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116810081/500000000 : ℝ)^129 ≤ (7230258637607/50000000000000 : ℝ)^97 := by
    have hnat : (116810081 : ℕ)^129*50000000000000^97 ≤ 7230258637607^97*500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116810081 500000000 7230258637607 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056008987/2000000000 : ℝ)^129 ≤ (21384870815627/50000000000000 : ℝ)^97 := by
    have hnat : (1056008987 : ℕ)^129*50000000000000^97 ≤ 21384870815627^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056008987 2000000000 21384870815627 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320011221/2500000000 : ℝ)^129 ≤ (167069301101/390625000000 : ℝ)^97 := by
    have hnat : (1320011221 : ℕ)^129*390625000000^97 ≤ 167069301101^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320011221 2500000000 167069301101 390625000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116810081/500000000 : ℝ), (1056008987/2000000000 : ℝ), (1320011221/2500000000 : ℝ)] ![(7230258637607/50000000000000 : ℝ), (21384870815627/50000000000000 : ℝ), (167069301101/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116810081/500000000 : ℝ)|^129 ≤ (7230258637607/50000000000000 : ℝ)^97
        have hw : |(-116810081/500000000 : ℝ)|=(116810081/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056008987/2000000000 : ℝ)|^129 ≤ (21384870815627/50000000000000 : ℝ)^97
        have hw : |(1056008987/2000000000 : ℝ)|=(1056008987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320011221/2500000000 : ℝ)|^129 ≤ (167069301101/390625000000 : ℝ)^97
        have hw : |(1320011221/2500000000 : ℝ)|=(1320011221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_5 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2682040571/5000000000 : ℝ)*x 0 + (-2225057789/10000000000 : ℝ)*x 1 + (528004489/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682040571/5000000000 : ℝ)^129 ≤ (272983693159/625000000000 : ℝ)^97 := by
    have hnat : (2682040571 : ℕ)^129*625000000000^97 ≤ 272983693159^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682040571 5000000000 272983693159 625000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225057789/10000000000 : ℝ)^129 ≤ (6776433971429/50000000000000 : ℝ)^97 := by
    have hnat : (2225057789 : ℕ)^129*50000000000000^97 ≤ 6776433971429^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225057789 10000000000 6776433971429 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528004489/1000000000 : ℝ)^129 ≤ (42769741146491/100000000000000 : ℝ)^97 := by
    have hnat : (528004489 : ℕ)^129*100000000000000^97 ≤ 42769741146491^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528004489 1000000000 42769741146491 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682040571/5000000000 : ℝ), (-2225057789/10000000000 : ℝ), (528004489/1000000000 : ℝ)] ![(272983693159/625000000000 : ℝ), (6776433971429/50000000000000 : ℝ), (42769741146491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682040571/5000000000 : ℝ)|^129 ≤ (272983693159/625000000000 : ℝ)^97
        have hw : |(2682040571/5000000000 : ℝ)|=(2682040571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2225057789/10000000000 : ℝ)|^129 ≤ (6776433971429/50000000000000 : ℝ)^97
        have hw : |(-2225057789/10000000000 : ℝ)|=(2225057789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528004489/1000000000 : ℝ)|^129 ≤ (42769741146491/100000000000000 : ℝ)^97
        have hw : |(528004489/1000000000 : ℝ)|=(528004489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_6 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1341020267/2500000000 : ℝ)*x 0 + (5280045053/10000000000 : ℝ)*x 1 + (-2225057669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341020267/2500000000 : ℝ)^129 ≤ (43677390104111/100000000000000 : ℝ)^97 := by
    have hnat : (1341020267 : ℕ)^129*100000000000000^97 ≤ 43677390104111^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341020267 2500000000 43677390104111 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280045053/10000000000 : ℝ)^129 ≤ (42769742902411/100000000000000 : ℝ)^97 := by
    have hnat : (5280045053 : ℕ)^129*100000000000000^97 ≤ 42769742902411^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280045053 10000000000 42769742902411 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225057669/10000000000 : ℝ)^129 ≤ (13552866970807/100000000000000 : ℝ)^97 := by
    have hnat : (2225057669 : ℕ)^129*100000000000000^97 ≤ 13552866970807^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225057669 10000000000 13552866970807 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341020267/2500000000 : ℝ), (5280045053/10000000000 : ℝ), (-2225057669/10000000000 : ℝ)] ![(43677390104111/100000000000000 : ℝ), (42769742902411/100000000000000 : ℝ), (13552866970807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341020267/2500000000 : ℝ)|^129 ≤ (43677390104111/100000000000000 : ℝ)^97
        have hw : |(1341020267/2500000000 : ℝ)|=(1341020267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280045053/10000000000 : ℝ)|^129 ≤ (42769742902411/100000000000000 : ℝ)^97
        have hw : |(5280045053/10000000000 : ℝ)|=(5280045053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2225057669/10000000000 : ℝ)|^129 ≤ (13552866970807/100000000000000 : ℝ)^97
        have hw : |(-2225057669/10000000000 : ℝ)|=(2225057669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_7 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4267173583/10000000000 : ℝ)*x 0 + (4432443903/10000000000 : ℝ)*x 1 + (4432443873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4267173583/10000000000 : ℝ)^129 ≤ (16109970537383/50000000000000 : ℝ)^97 := by
    have hnat : (4267173583 : ℕ)^129*50000000000000^97 ≤ 16109970537383^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267173583 10000000000 16109970537383 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4432443903/10000000000 : ℝ)^129 ≤ (6778005920819/20000000000000 : ℝ)^97 := by
    have hnat : (4432443903 : ℕ)^129*20000000000000^97 ≤ 6778005920819^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432443903 10000000000 6778005920819 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4432443873/10000000000 : ℝ)^129 ≤ (4236253662381/12500000000000 : ℝ)^97 := by
    have hnat : (4432443873 : ℕ)^129*12500000000000^97 ≤ 4236253662381^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432443873 10000000000 4236253662381 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4267173583/10000000000 : ℝ), (4432443903/10000000000 : ℝ), (4432443873/10000000000 : ℝ)] ![(16109970537383/50000000000000 : ℝ), (6778005920819/20000000000000 : ℝ), (4236253662381/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4267173583/10000000000 : ℝ)|^129 ≤ (16109970537383/50000000000000 : ℝ)^97
        have hw : |(4267173583/10000000000 : ℝ)|=(4267173583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4432443903/10000000000 : ℝ)|^129 ≤ (6778005920819/20000000000000 : ℝ)^97
        have hw : |(4432443903/10000000000 : ℝ)|=(4432443903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4432443873/10000000000 : ℝ)|^129 ≤ (4236253662381/12500000000000 : ℝ)^97
        have hw : |(4432443873/10000000000 : ℝ)|=(4432443873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_8 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2852273/12500000 : ℝ)*x 0 + (5213982677/10000000000 : ℝ)*x 1 + (215480429/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2852273/12500000 : ℝ)^129 ≤ (437955527301/3125000000000 : ℝ)^97 := by
    have hnat : (2852273 : ℕ)^129*3125000000000^97 ≤ 437955527301^97*12500000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852273 12500000 437955527301 3125000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213982677/10000000000 : ℝ)^129 ≤ (10514889499689/25000000000000 : ℝ)^97 := by
    have hnat : (5213982677 : ℕ)^129*25000000000000^97 ≤ 10514889499689^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213982677 10000000000 10514889499689 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215480429/400000000 : ℝ)^129 ≤ (43925865105949/100000000000000 : ℝ)^97 := by
    have hnat : (215480429 : ℕ)^129*100000000000000^97 ≤ 43925865105949^97*400000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215480429 400000000 43925865105949 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2852273/12500000 : ℝ), (5213982677/10000000000 : ℝ), (215480429/400000000 : ℝ)] ![(437955527301/3125000000000 : ℝ), (10514889499689/25000000000000 : ℝ), (43925865105949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2852273/12500000 : ℝ)|^129 ≤ (437955527301/3125000000000 : ℝ)^97
        have hw : |(-2852273/12500000 : ℝ)|=(2852273/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213982677/10000000000 : ℝ)|^129 ≤ (10514889499689/25000000000000 : ℝ)^97
        have hw : |(5213982677/10000000000 : ℝ)|=(5213982677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215480429/400000000 : ℝ)|^129 ≤ (43925865105949/100000000000000 : ℝ)^97
        have hw : |(215480429/400000000 : ℝ)|=(215480429/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_9 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2644185223/5000000000 : ℝ)*x 0 + (-34112161/156250000 : ℝ)*x 1 + (673376333/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644185223/5000000000 : ℝ)^129 ≤ (2678715726013/6250000000000 : ℝ)^97 := by
    have hnat : (2644185223 : ℕ)^129*6250000000000^97 ≤ 2678715726013^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644185223 5000000000 2678715726013 6250000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34112161/156250000 : ℝ)^129 ≤ (6607341965193/50000000000000 : ℝ)^97 := by
    have hnat : (34112161 : ℕ)^129*50000000000000^97 ≤ 6607341965193^97*156250000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34112161 156250000 6607341965193 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673376333/1250000000 : ℝ)^129 ≤ (43925864444463/100000000000000 : ℝ)^97 := by
    have hnat : (673376333 : ℕ)^129*100000000000000^97 ≤ 43925864444463^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673376333 1250000000 43925864444463 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644185223/5000000000 : ℝ), (-34112161/156250000 : ℝ), (673376333/1250000000 : ℝ)] ![(2678715726013/6250000000000 : ℝ), (6607341965193/50000000000000 : ℝ), (43925864444463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644185223/5000000000 : ℝ)|^129 ≤ (2678715726013/6250000000000 : ℝ)^97
        have hw : |(2644185223/5000000000 : ℝ)|=(2644185223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34112161/156250000 : ℝ)|^129 ≤ (6607341965193/50000000000000 : ℝ)^97
        have hw : |(-34112161/156250000 : ℝ)|=(34112161/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673376333/1250000000 : ℝ)|^129 ≤ (43925864444463/100000000000000 : ℝ)^97
        have hw : |(673376333/1250000000 : ℝ)|=(673376333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_10 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1057674107/2000000000 : ℝ)*x 0 + (1346752671/2500000000 : ℝ)*x 1 + (-1091589079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057674107/2000000000 : ℝ)^129 ≤ (2142972628773/5000000000000 : ℝ)^97 := by
    have hnat : (1057674107 : ℕ)^129*5000000000000^97 ≤ 2142972628773^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057674107 2000000000 2142972628773 5000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346752671/2500000000 : ℝ)^129 ≤ (1372683270667/3125000000000 : ℝ)^97 := by
    have hnat : (1346752671 : ℕ)^129*3125000000000^97 ≤ 1372683270667^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346752671 2500000000 1372683270667 3125000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091589079/5000000000 : ℝ)^129 ≤ (6607341377557/50000000000000 : ℝ)^97 := by
    have hnat : (1091589079 : ℕ)^129*50000000000000^97 ≤ 6607341377557^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091589079 5000000000 6607341377557 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057674107/2000000000 : ℝ), (1346752671/2500000000 : ℝ), (-1091589079/5000000000 : ℝ)] ![(2142972628773/5000000000000 : ℝ), (1372683270667/3125000000000 : ℝ), (6607341377557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057674107/2000000000 : ℝ)|^129 ≤ (2142972628773/5000000000000 : ℝ)^97
        have hw : |(1057674107/2000000000 : ℝ)|=(1057674107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346752671/2500000000 : ℝ)|^129 ≤ (1372683270667/3125000000000 : ℝ)^97
        have hw : |(1346752671/2500000000 : ℝ)|=(1346752671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091589079/5000000000 : ℝ)|^129 ≤ (6607341377557/50000000000000 : ℝ)^97
        have hw : |(-1091589079/5000000000 : ℝ)|=(1091589079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_11 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4505490013/10000000000 : ℝ)*x 0 + (2156583277/5000000000 : ℝ)*x 1 + (43131667/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4505490013/10000000000 : ℝ)^129 ≤ (6926958632661/20000000000000 : ℝ)^97 := by
    have hnat : (4505490013 : ℕ)^129*20000000000000^97 ≤ 6926958632661^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505490013 10000000000 6926958632661 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156583277/5000000000 : ℝ)^129 ≤ (16341301338687/50000000000000 : ℝ)^97 := by
    have hnat : (2156583277 : ℕ)^129*50000000000000^97 ≤ 16341301338687^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156583277 5000000000 16341301338687 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43131667/100000000 : ℝ)^129 ≤ (204266275929/625000000000 : ℝ)^97 := by
    have hnat : (43131667 : ℕ)^129*625000000000^97 ≤ 204266275929^97*100000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43131667 100000000 204266275929 625000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4505490013/10000000000 : ℝ), (2156583277/5000000000 : ℝ), (43131667/100000000 : ℝ)] ![(6926958632661/20000000000000 : ℝ), (16341301338687/50000000000000 : ℝ), (204266275929/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4505490013/10000000000 : ℝ)|^129 ≤ (6926958632661/20000000000000 : ℝ)^97
        have hw : |(4505490013/10000000000 : ℝ)|=(4505490013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2156583277/5000000000 : ℝ)|^129 ≤ (16341301338687/50000000000000 : ℝ)^97
        have hw : |(2156583277/5000000000 : ℝ)|=(2156583277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43131667/100000000 : ℝ)|^129 ≤ (204266275929/625000000000 : ℝ)^97
        have hw : |(43131667/100000000 : ℝ)|=(43131667/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_12 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-426086171/2000000000 : ℝ)*x 0 + (1360533701/2500000000 : ℝ)*x 1 + (131801123/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426086171/2000000000 : ℝ)^129 ≤ (6395889237967/50000000000000 : ℝ)^97 := by
    have hnat : (426086171 : ℕ)^129*50000000000000^97 ≤ 6395889237967^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426086171 2000000000 6395889237967 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360533701/2500000000 : ℝ)^129 ≤ (356197108717/800000000000 : ℝ)^97 := by
    have hnat : (1360533701 : ℕ)^129*800000000000^97 ≤ 356197108717^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360533701 2500000000 356197108717 800000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131801123/250000000 : ℝ)^129 ≤ (42683582919613/100000000000000 : ℝ)^97 := by
    have hnat : (131801123 : ℕ)^129*100000000000000^97 ≤ 42683582919613^97*250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131801123 250000000 42683582919613 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426086171/2000000000 : ℝ), (1360533701/2500000000 : ℝ), (131801123/250000000 : ℝ)] ![(6395889237967/50000000000000 : ℝ), (356197108717/800000000000 : ℝ), (42683582919613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426086171/2000000000 : ℝ)|^129 ≤ (6395889237967/50000000000000 : ℝ)^97
        have hw : |(-426086171/2000000000 : ℝ)|=(426086171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360533701/2500000000 : ℝ)|^129 ≤ (356197108717/800000000000 : ℝ)^97
        have hw : |(1360533701/2500000000 : ℝ)|=(1360533701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131801123/250000000 : ℝ)|^129 ≤ (42683582919613/100000000000000 : ℝ)^97
        have hw : |(131801123/250000000 : ℝ)|=(131801123/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_13 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5369740611/10000000000 : ℝ)*x 0 + (-557031363/2500000000 : ℝ)*x 1 + (659005701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369740611/10000000000 : ℝ)^129 ≤ (43738686684181/100000000000000 : ℝ)^97 := by
    have hnat : (5369740611 : ℕ)^129*100000000000000^97 ≤ 43738686684181^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369740611 10000000000 43738686684181 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557031363/2500000000 : ℝ)^129 ≤ (6788861485477/50000000000000 : ℝ)^97 := by
    have hnat : (557031363 : ℕ)^129*50000000000000^97 ≤ 6788861485477^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557031363 2500000000 6788861485477 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659005701/1250000000 : ℝ)^129 ≤ (8536718065479/20000000000000 : ℝ)^97 := by
    have hnat : (659005701 : ℕ)^129*20000000000000^97 ≤ 8536718065479^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659005701 1250000000 8536718065479 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369740611/10000000000 : ℝ), (-557031363/2500000000 : ℝ), (659005701/1250000000 : ℝ)] ![(43738686684181/100000000000000 : ℝ), (6788861485477/50000000000000 : ℝ), (8536718065479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369740611/10000000000 : ℝ)|^129 ≤ (43738686684181/100000000000000 : ℝ)^97
        have hw : |(5369740611/10000000000 : ℝ)|=(5369740611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557031363/2500000000 : ℝ)|^129 ≤ (6788861485477/50000000000000 : ℝ)^97
        have hw : |(-557031363/2500000000 : ℝ)|=(557031363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659005701/1250000000 : ℝ)|^129 ≤ (8536718065479/20000000000000 : ℝ)^97
        have hw : |(659005701/1250000000 : ℝ)|=(659005701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_14 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1342435107/2500000000 : ℝ)*x 0 + (5272045267/10000000000 : ℝ)*x 1 + (-44562523/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342435107/2500000000 : ℝ)^129 ≤ (1749547388073/4000000000000 : ℝ)^97 := by
    have hnat : (1342435107 : ℕ)^129*4000000000000^97 ≤ 1749547388073^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342435107 2500000000 1749547388073 4000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272045267/10000000000 : ℝ)^129 ≤ (8536717331161/20000000000000 : ℝ)^97 := by
    have hnat : (5272045267 : ℕ)^129*20000000000000^97 ≤ 8536717331161^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272045267 10000000000 8536717331161 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44562523/200000000 : ℝ)^129 ≤ (13577728627623/100000000000000 : ℝ)^97 := by
    have hnat : (44562523 : ℕ)^129*100000000000000^97 ≤ 13577728627623^97*200000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44562523 200000000 13577728627623 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342435107/2500000000 : ℝ), (5272045267/10000000000 : ℝ), (-44562523/200000000 : ℝ)] ![(1749547388073/4000000000000 : ℝ), (8536717331161/20000000000000 : ℝ), (13577728627623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342435107/2500000000 : ℝ)|^129 ≤ (1749547388073/4000000000000 : ℝ)^97
        have hw : |(1342435107/2500000000 : ℝ)|=(1342435107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272045267/10000000000 : ℝ)|^129 ≤ (8536717331161/20000000000000 : ℝ)^97
        have hw : |(5272045267/10000000000 : ℝ)|=(5272045267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44562523/200000000 : ℝ)|^129 ≤ (13577728627623/100000000000000 : ℝ)^97
        have hw : |(-44562523/200000000 : ℝ)|=(44562523/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_box_15 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2124550077/5000000000 : ℝ)*x 0 + (888271753/2000000000 : ℝ)*x 1 + (888271779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124550077/5000000000 : ℝ)^129 ≤ (32038582055067/100000000000000 : ℝ)^97 := by
    have hnat : (2124550077 : ℕ)^129*100000000000000^97 ≤ 32038582055067^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124550077 5000000000 32038582055067 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888271753/2000000000 : ℝ)^129 ≤ (6796141661127/20000000000000 : ℝ)^97 := by
    have hnat : (888271753 : ℕ)^129*20000000000000^97 ≤ 6796141661127^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888271753 2000000000 6796141661127 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888271779/2000000000 : ℝ)^129 ≤ (6796141925677/20000000000000 : ℝ)^97 := by
    have hnat : (888271779 : ℕ)^129*20000000000000^97 ≤ 6796141925677^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888271779 2000000000 6796141925677 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124550077/5000000000 : ℝ), (888271753/2000000000 : ℝ), (888271779/2000000000 : ℝ)] ![(32038582055067/100000000000000 : ℝ), (6796141661127/20000000000000 : ℝ), (6796141925677/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124550077/5000000000 : ℝ)|^129 ≤ (32038582055067/100000000000000 : ℝ)^97
        have hw : |(2124550077/5000000000 : ℝ)|=(2124550077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(888271753/2000000000 : ℝ)|^129 ≤ (6796141661127/20000000000000 : ℝ)^97
        have hw : |(888271753/2000000000 : ℝ)|=(888271753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(888271779/2000000000 : ℝ)|^129 ≤ (6796141925677/20000000000000 : ℝ)^97
        have hw : |(888271779/2000000000 : ℝ)|=(888271779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1063_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29619/50000 : ℝ) ∧ (79563/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41473/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (703/6250 : ℝ) ^ (8255/2048 : ℝ) ≤ (2993234014871741/20000000000000000000 : ℝ) := by
    have hpowers : (703/6250 : ℝ)^8255 ≤ (2993234014871741/20000000000000000000 : ℝ)^2048 := by
      have hnat : (703 : ℕ)^8255*20000000000000000000^2048 ≤ 2993234014871741^2048*6250^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 6250 2993234014871741 20000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/6250 : ℝ)) (X := (2993234014871741/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14001/100000 : ℝ) ^ (8255/2048 : ℝ) ≤ (36171840523481333/100000000000000000000 : ℝ) := by
    have hpowers : (14001/100000 : ℝ)^8255 ≤ (36171840523481333/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14001 : ℕ)^8255*100000000000000000000^2048 ≤ 36171840523481333^2048*100000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14001 100000 36171840523481333 100000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14001/100000 : ℝ)) (X := (36171840523481333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002993234014871741/10000000000000000000 : ℝ) ≤ (10000742514057763/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (10002993234014871741/10000000000000000000 : ℝ)^2048 ≤ (10000742514057763/10000000000000000 : ℝ)^8255 := by
      have hnat : (10002993234014871741 : ℕ)^2048*10000000000000000^8255 ≤ 10000742514057763^8255*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002993234014871741 10000000000000000000 10000742514057763 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000742514057763/10000000000000000 : ℝ)) (X := (10002993234014871741/10000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025569005298920019/50000000000000000000 : ℝ) ≤ (10001268449626713/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50025569005298920019/50000000000000000000 : ℝ)^2048 ≤ (10001268449626713/10000000000000000 : ℝ)^8255 := by
      have hnat : (50025569005298920019 : ℕ)^2048*10000000000000000^8255 ≤ 10001268449626713^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025569005298920019 50000000000000000000 10001268449626713 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001268449626713/10000000000000000 : ℝ)) (X := (50025569005298920019/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036171840523481333/50000000000000000000 : ℝ) ≤ (10001794385195663/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50036171840523481333/50000000000000000000 : ℝ)^2048 ≤ (10001794385195663/10000000000000000 : ℝ)^8255 := by
      have hnat : (50036171840523481333 : ℕ)^2048*10000000000000000^8255 ≤ 10001794385195663^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036171840523481333 50000000000000000000 10001794385195663 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001794385195663/10000000000000000 : ℝ)) (X := (50036171840523481333/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2993234014871741/20000000000000000000 : ℝ) ≤ ((27520212694641922339/27530000000000000000 : ℝ)+2*(10518711379/5506000000000 : ℝ)*(703/6250 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (27520212694641922339/27530000000000000000 : ℝ)+2*(10518711379/5506000000000 : ℝ)*(703/6250 : ℝ)=(10000742514057763/10000000000000000 : ℝ) by norm_num, show 1+2*(2993234014871741/20000000000000000000 : ℝ)=(10002993234014871741/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36171840523481333/100000000000000000000 : ℝ)+(2993234014871741/20000000000000000000 : ℝ) ≤ ((27520212694641922339/27530000000000000000 : ℝ)+(10518711379/5506000000000 : ℝ)*((14001/100000 : ℝ)+(703/6250 : ℝ)))^(8255/2048 : ℝ) := by
    rw [show (27520212694641922339/27530000000000000000 : ℝ)+(10518711379/5506000000000 : ℝ)*((14001/100000 : ℝ)+(703/6250 : ℝ))=(10001268449626713/10000000000000000 : ℝ) by norm_num, show 1+(36171840523481333/100000000000000000000 : ℝ)+(2993234014871741/20000000000000000000 : ℝ)=(50025569005298920019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36171840523481333/100000000000000000000 : ℝ) ≤ ((27520212694641922339/27530000000000000000 : ℝ)+2*(10518711379/5506000000000 : ℝ)*(14001/100000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (27520212694641922339/27530000000000000000 : ℝ)+2*(10518711379/5506000000000 : ℝ)*(14001/100000 : ℝ)=(10001794385195663/10000000000000000 : ℝ) by norm_num, show 1+2*(36171840523481333/100000000000000000000 : ℝ)=(50036171840523481333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27520212694641922339/27530000000000000000 : ℝ)*(X 1 0+X 2 0)+(10518711379/5506000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (27520212694641922339/27530000000000000000 : ℝ)) (alpha := (10518711379/5506000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27520212694641922339/27530000000000000000 : ℝ)*(X 0 1+X 2 1)+(10518711379/5506000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (27520212694641922339/27530000000000000000 : ℝ)) (alpha := (10518711379/5506000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27520212694641922339/27530000000000000000 : ℝ)*(X 0 2+X 1 2)+(10518711379/5506000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (27520212694641922339/27530000000000000000 : ℝ)) (alpha := (10518711379/5506000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-415135413/2000000000 : ℝ)*X 0 0+(672176283/1250000000 : ℝ)*X 0 1+(5377409957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295169191/10000000000 : ℝ)*X 1 0+(-546750347/2500000000 : ℝ)*X 1 1+(537741019/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((82737019/156250000 : ℝ)*X 2 0+(2688705021/5000000000 : ℝ)*X 2 1+(-1093500777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2242174473/5000000000 : ℝ)*X 0 0+(2161938881/5000000000 : ℝ)*X 0 1+(4323877623/10000000000 : ℝ)*X 0 2+(2242174473/5000000000 : ℝ)*X 1 0+(2161938881/5000000000 : ℝ)*X 1 1+(4323877623/10000000000 : ℝ)*X 1 2+(2242174473/5000000000 : ℝ)*X 2 0+(2161938881/5000000000 : ℝ)*X 2 1+(4323877623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-116810081/500000000 : ℝ)*X 0 0+(1056008987/2000000000 : ℝ)*X 0 1+(1320011221/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682040571/5000000000 : ℝ)*X 1 0+(-2225057789/10000000000 : ℝ)*X 1 1+(528004489/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1341020267/2500000000 : ℝ)*X 2 0+(5280045053/10000000000 : ℝ)*X 2 1+(-2225057669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4267173583/10000000000 : ℝ)*X 0 0+(4432443903/10000000000 : ℝ)*X 0 1+(4432443873/10000000000 : ℝ)*X 0 2+(4267173583/10000000000 : ℝ)*X 1 0+(4432443903/10000000000 : ℝ)*X 1 1+(4432443873/10000000000 : ℝ)*X 1 2+(4267173583/10000000000 : ℝ)*X 2 0+(4432443903/10000000000 : ℝ)*X 2 1+(4432443873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2852273/12500000 : ℝ)*X 0 0+(5213982677/10000000000 : ℝ)*X 0 1+(215480429/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644185223/5000000000 : ℝ)*X 1 0+(-34112161/156250000 : ℝ)*X 1 1+(673376333/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057674107/2000000000 : ℝ)*X 2 0+(1346752671/2500000000 : ℝ)*X 2 1+(-1091589079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4505490013/10000000000 : ℝ)*X 0 0+(2156583277/5000000000 : ℝ)*X 0 1+(43131667/100000000 : ℝ)*X 0 2+(4505490013/10000000000 : ℝ)*X 1 0+(2156583277/5000000000 : ℝ)*X 1 1+(43131667/100000000 : ℝ)*X 1 2+(4505490013/10000000000 : ℝ)*X 2 0+(2156583277/5000000000 : ℝ)*X 2 1+(43131667/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-426086171/2000000000 : ℝ)*X 0 0+(1360533701/2500000000 : ℝ)*X 0 1+(131801123/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369740611/10000000000 : ℝ)*X 1 0+(-557031363/2500000000 : ℝ)*X 1 1+(659005701/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342435107/2500000000 : ℝ)*X 2 0+(5272045267/10000000000 : ℝ)*X 2 1+(-44562523/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2124550077/5000000000 : ℝ)*X 0 0+(888271753/2000000000 : ℝ)*X 0 1+(888271779/2000000000 : ℝ)*X 0 2+(2124550077/5000000000 : ℝ)*X 1 0+(888271753/2000000000 : ℝ)*X 1 1+(888271779/2000000000 : ℝ)*X 1 2+(2124550077/5000000000 : ℝ)*X 2 0+(888271753/2000000000 : ℝ)*X 2 1+(888271779/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-214121093232360871024683920670213/344125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9465519/50000000000000 : ℝ)*(upper1) + (9661163/50000000000000 : ℝ)*(upper4) + (2584507/6250000000000 : ℝ)*(upper5) + (963488352487811/25000000000000 : ℝ)*(major0) + (963488352487811/25000000000000 : ℝ)*(major1) + (963488352487811/25000000000000 : ℝ)*(major2) + (3060153057/100000000000000 : ℝ)*(sp1) + (240858367/20000000000000 : ℝ)*(sp3) + (5123470255552969/100000000000000 : ℝ)*(sp4) + (2561736019052143/50000000000000 : ℝ)*(sp5) + (5123411225434021/100000000000000 : ℝ)*(sp6) + (1302585574367771/50000000000000 : ℝ)*(sp7) + (2421352187/50000000000000 : ℝ)*(sp8) + (63872823321/100000000000000 : ℝ)*(sp14) + (2605172353027377/100000000000000 : ℝ)*(f.failure) + (2561737549128671/50000000000000 : ℝ)*(f.sum) + (1961885632803/688250000000000000000000000 : ℝ)*base65 + (2357593124331859929/688250000000000000000000000000000 : ℝ)*base67 + (2812767806925859929/688250000000000000000000000000000 : ℝ)*base69 + (2728931911907640071/688250000000000000000000000000000 : ℝ)*base72 + (16319160083741/1376500000000000000000000000 : ℝ)*base73 + (594742542792140071/688250000000000000000000000000000 : ℝ)*base76 + (162650225582890071/688250000000000000000000000000000 : ℝ)*base78 + (604241614435890071/688250000000000000000000000000000 : ℝ)*base80 + (2523363672939/688250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (761737/10000000000000000000000 : ℝ)*base89 + (761737/10000000000000000000000 : ℝ)*base91 + (761737/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29619/50000 : ℝ) ≤ (3185358930335974477940382178389/5376953125000000000000000000000 : ℝ) := by norm_num
    linear_combination (27122147/100000000000000 : ℝ)*(upper2) + (33003143/50000000000000 : ℝ)*(upper3) + (17199011/50000000000000 : ℝ)*(lower5) + (122400551707363/3125000000000 : ℝ)*(major0) + (122400551707363/3125000000000 : ℝ)*(major1) + (122400551707363/3125000000000 : ℝ)*(major2) + (5166216858755283/100000000000000 : ℝ)*(sp0) + (258310811666597/5000000000000 : ℝ)*(sp1) + (5166214568387971/100000000000000 : ℝ)*(sp2) + (661916562821327/25000000000000 : ℝ)*(sp3) + (256937213/5000000000000 : ℝ)*(sp5) + (348752581/50000000000000 : ℝ)*(sp7) + (4513320917/100000000000000 : ℝ)*(sp8) + (6803688229/100000000000000 : ℝ)*(sp10) + (264766694879047/10000000000000 : ℝ)*(f.failure) + (25831106860381/500000000000 : ℝ)*(f.sum) + (11506290598467/2753000000000000000000000000 : ℝ)*base66 + (222204514043013307/86031250000000000000000000000000 : ℝ)*base67 + (483456001241794557/86031250000000000000000000000000 : ℝ)*base69 + (810890654150419557/86031250000000000000000000000000 : ℝ)*base71 + (9005397943387/1376500000000000000000000000 : ℝ)*base73 + (813651479897044557/86031250000000000000000000000000 : ℝ)*base75 + (315107375755950807/86031250000000000000000000000000 : ℝ)*base77 + (464187716904232057/86031250000000000000000000000000 : ℝ)*base79 + (3295765983721/1376500000000000000000000000 : ℝ)*base82 + (8470993/1000000000000000000000 : ℝ)*base90 + (8470993/1000000000000000000000 : ℝ)*base92 + (8470993/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79563/100000 : ℝ) ≤ (21904312908470175243466069918401/27530000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48774223/100000000000000 : ℝ)*(upper0) + (32463763/50000000000000 : ℝ)*(lower3) + (19061551/25000000000000 : ℝ)*(upper4) + (87701224374851/2000000000000 : ℝ)*(major0) + (87701224374851/2000000000000 : ℝ)*(major1) + (87701224374851/2000000000000 : ℝ)*(major2) + (4367863329/10000000000000 : ℝ)*(sp1) + (10021321627/12500000000000 : ℝ)*(sp2) + (2512436531/6250000000000 : ℝ)*(sp3) + (114620267/10000000000000 : ℝ)*(sp4) + (1155882422366821/20000000000000 : ℝ)*(sp8) + (1155873915880697/20000000000000 : ℝ)*(sp9) + (5779333087463759/100000000000000 : ℝ)*(sp10) + (1482073615484077/50000000000000 : ℝ)*(sp11) + (59283748599053/2000000000000 : ℝ)*(f.failure) + (231176530321471/4000000000000 : ℝ)*(f.sum) + (3153326812227/1376500000000000000000000000 : ℝ)*base66 + (215053324841483511/55060000000000000000000000000000 : ℝ)*base68 + (822307114176083511/55060000000000000000000000000000 : ℝ)*base70 + (451447109273383511/55060000000000000000000000000000 : ℝ)*base72 + (5325610705303/344125000000000000000000000 : ℝ)*base74 + (852952008965183511/55060000000000000000000000000000 : ℝ)*base76 + (550612582057643511/55060000000000000000000000000000 : ℝ)*base78 + (377130820094063511/55060000000000000000000000000000 : ℝ)*base80 + (7016656041033/1376500000000000000000000000 : ℝ)*base82 + (2457093/200000000000000000000 : ℝ)*base89 + (2457093/200000000000000000000 : ℝ)*base91 + (2457093/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41473/50000 : ℝ) ≤ (-570856468062385844908715158436049/688250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (926709/4000000000000 : ℝ)*(lower0) + (8841711/4000000000000 : ℝ)*(upper3) + (342424183/100000000000000 : ℝ)*(lower4) + (2209788877032099/50000000000000 : ℝ)*(major0) + (2209788877032099/50000000000000 : ℝ)*(major1) + (2209788877032099/50000000000000 : ℝ)*(major2) + (19750953261/100000000000000 : ℝ)*(sp0) + (7705085491/25000000000000 : ℝ)*(sp5) + (445767669171/100000000000000 : ℝ)*(sp6) + (80793281939/50000000000000 : ℝ)*(sp7) + (2939631887261771/50000000000000 : ℝ)*(sp12) + (5879252705134839/100000000000000 : ℝ)*(sp13) + (5878837757807633/100000000000000 : ℝ)*(sp14) + (373419765536283/12500000000000 : ℝ)*(sp15) + (1493759855427071/50000000000000 : ℝ)*(f.failure) + (1469820881369201/25000000000000 : ℝ)*(f.sum) + (1080146100059/550600000000000000000000000 : ℝ)*base66 + (6635703576524159561/1376500000000000000000000000000000 : ℝ)*base67 + (15004799178061659561/1376500000000000000000000000000000 : ℝ)*base69 + (18481589229777659561/1376500000000000000000000000000000 : ℝ)*base71 + (1835564481301/275300000000000000000000000 : ℝ)*base73 + (13485178065454159561/1376500000000000000000000000000000 : ℝ)*base75 + (13082196353600159561/1376500000000000000000000000000000 : ℝ)*base77 + (4416706562671159561/1376500000000000000000000000000000 : ℝ)*base79 + (298664068879/550600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (32850649/5000000000000000000000 : ℝ)*base90 + (32850649/5000000000000000000000 : ℝ)*base92 + (32850649/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1063_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29619/50000 : ℝ) else (79563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41473/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1063_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1063_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29619/50000 : ℝ) else (79563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41473/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1063_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1063_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(29619/50000 : ℝ) else (79563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41473/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1063_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
