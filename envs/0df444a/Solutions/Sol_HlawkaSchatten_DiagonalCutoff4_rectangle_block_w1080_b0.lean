-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1080_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:48:59.442654+00:00
-- url     : https://prove2.me/submissions/25eb96ec-2374-48a3-aac0-5efe7f8c16b9

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
theorem support_rectangle_w1080_s0_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-477897587/2500000000 : ℝ)*x 0 + (6068771331/10000000000 : ℝ)*x 1 + (2386290377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477897587/2500000000 : ℝ)^8273 ≤ (11091150890413/100000000000000 : ℝ)^6225 := by
    have hnat : (477897587 : ℕ)^8273*100000000000000^6225 ≤ 11091150890413^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477897587 2500000000 11091150890413 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6068771331/10000000000 : ℝ)^8273 ≤ (10298448346331/20000000000000 : ℝ)^6225 := by
    have hnat : (6068771331 : ℕ)^8273*20000000000000^6225 ≤ 10298448346331^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6068771331 10000000000 10298448346331 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386290377/5000000000 : ℝ)^8273 ≤ (37416607367013/100000000000000 : ℝ)^6225 := by
    have hnat : (2386290377 : ℕ)^8273*100000000000000^6225 ≤ 37416607367013^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386290377 5000000000 37416607367013 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-477897587/2500000000 : ℝ), (6068771331/10000000000 : ℝ), (2386290377/5000000000 : ℝ)] ![(11091150890413/100000000000000 : ℝ), (10298448346331/20000000000000 : ℝ), (37416607367013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-477897587/2500000000 : ℝ)|^8273 ≤ (11091150890413/100000000000000 : ℝ)^6225
        have hw : |(-477897587/2500000000 : ℝ)|=(477897587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6068771331/10000000000 : ℝ)|^8273 ≤ (10298448346331/20000000000000 : ℝ)^6225
        have hw : |(6068771331/10000000000 : ℝ)|=(6068771331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386290377/5000000000 : ℝ)|^8273 ≤ (37416607367013/100000000000000 : ℝ)^6225
        have hw : |(2386290377/5000000000 : ℝ)|=(2386290377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s0_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (690035533/1250000000 : ℝ)*x 0 + (-664317403/2500000000 : ℝ)*x 1 + (954516237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690035533/1250000000 : ℝ)^8273 ≤ (22700624093529/50000000000000 : ℝ)^6225 := by
    have hnat : (690035533 : ℕ)^8273*50000000000000^6225 ≤ 22700624093529^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690035533 1250000000 22700624093529 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (664317403/2500000000 : ℝ)^8273 ≤ (17182139942097/100000000000000 : ℝ)^6225 := by
    have hnat : (664317403 : ℕ)^8273*100000000000000^6225 ≤ 17182139942097^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664317403 2500000000 17182139942097 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954516237/2000000000 : ℝ)^8273 ≤ (9354152964423/25000000000000 : ℝ)^6225 := by
    have hnat : (954516237 : ℕ)^8273*25000000000000^6225 ≤ 9354152964423^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954516237 2000000000 9354152964423 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690035533/1250000000 : ℝ), (-664317403/2500000000 : ℝ), (954516237/2000000000 : ℝ)] ![(22700624093529/50000000000000 : ℝ), (17182139942097/100000000000000 : ℝ), (9354152964423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690035533/1250000000 : ℝ)|^8273 ≤ (22700624093529/50000000000000 : ℝ)^6225
        have hw : |(690035533/1250000000 : ℝ)|=(690035533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-664317403/2500000000 : ℝ)|^8273 ≤ (17182139942097/100000000000000 : ℝ)^6225
        have hw : |(-664317403/2500000000 : ℝ)|=(664317403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(954516237/2000000000 : ℝ)|^8273 ≤ (9354152964423/25000000000000 : ℝ)^6225
        have hw : |(954516237/2000000000 : ℝ)|=(954516237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s0_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (138007119/250000000 : ℝ)*x 0 + (4772581613/10000000000 : ℝ)*x 1 + (-1328634231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138007119/250000000 : ℝ)^8273 ≤ (45401253608461/100000000000000 : ℝ)^6225 := by
    have hnat : (138007119 : ℕ)^8273*100000000000000^6225 ≤ 45401253608461^6225*250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138007119 250000000 45401253608461 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4772581613/10000000000 : ℝ)^8273 ≤ (18708308158557/50000000000000 : ℝ)^6225 := by
    have hnat : (4772581613 : ℕ)^8273*50000000000000^6225 ≤ 18708308158557^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772581613 10000000000 18708308158557 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328634231/5000000000 : ℝ)^8273 ≤ (8591065029841/50000000000000 : ℝ)^6225 := by
    have hnat : (1328634231 : ℕ)^8273*50000000000000^6225 ≤ 8591065029841^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328634231 5000000000 8591065029841 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(138007119/250000000 : ℝ), (4772581613/10000000000 : ℝ), (-1328634231/5000000000 : ℝ)] ![(45401253608461/100000000000000 : ℝ), (18708308158557/50000000000000 : ℝ), (8591065029841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(138007119/250000000 : ℝ)|^8273 ≤ (45401253608461/100000000000000 : ℝ)^6225
        have hw : |(138007119/250000000 : ℝ)|=(138007119/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4772581613/10000000000 : ℝ)|^8273 ≤ (18708308158557/50000000000000 : ℝ)^6225
        have hw : |(4772581613/10000000000 : ℝ)|=(4772581613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1328634231/5000000000 : ℝ)|^8273 ≤ (8591065029841/50000000000000 : ℝ)^6225
        have hw : |(-1328634231/5000000000 : ℝ)|=(1328634231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s0_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2103026393/5000000000 : ℝ)*x 0 + (312412861/1000000000 : ℝ)*x 1 + (708942717/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103026393/5000000000 : ℝ)^8273 ≤ (31632317552001/100000000000000 : ℝ)^6225 := by
    have hnat : (2103026393 : ℕ)^8273*100000000000000^6225 ≤ 31632317552001^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103026393 5000000000 31632317552001 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312412861/1000000000 : ℝ)^8273 ≤ (21305745875461/100000000000000 : ℝ)^6225 := by
    have hnat : (312412861 : ℕ)^8273*100000000000000^6225 ≤ 21305745875461^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312412861 1000000000 21305745875461 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708942717/1250000000 : ℝ)^8273 ≤ (9412387311091/20000000000000 : ℝ)^6225 := by
    have hnat : (708942717 : ℕ)^8273*20000000000000^6225 ≤ 9412387311091^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708942717 1250000000 9412387311091 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103026393/5000000000 : ℝ), (312412861/1000000000 : ℝ), (708942717/1250000000 : ℝ)] ![(31632317552001/100000000000000 : ℝ), (21305745875461/100000000000000 : ℝ), (9412387311091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103026393/5000000000 : ℝ)|^8273 ≤ (31632317552001/100000000000000 : ℝ)^6225
        have hw : |(2103026393/5000000000 : ℝ)|=(2103026393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312412861/1000000000 : ℝ)|^8273 ≤ (21305745875461/100000000000000 : ℝ)^6225
        have hw : |(312412861/1000000000 : ℝ)|=(312412861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708942717/1250000000 : ℝ)|^8273 ≤ (9412387311091/20000000000000 : ℝ)^6225
        have hw : |(708942717/1250000000 : ℝ)|=(708942717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s0_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-239615093/1250000000 : ℝ)*x 0 + (961208957/2000000000 : ℝ)*x 1 + (37713349/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239615093/1250000000 : ℝ)^8273 ≤ (1113227191879/10000000000000 : ℝ)^6225 := by
    have hnat : (239615093 : ℕ)^8273*10000000000000^6225 ≤ 1113227191879^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239615093 1250000000 1113227191879 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961208957/2000000000 : ℝ)^8273 ≤ (37765677662977/100000000000000 : ℝ)^6225 := by
    have hnat : (961208957 : ℕ)^8273*100000000000000^6225 ≤ 37765677662977^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961208957 2000000000 37765677662977 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37713349/62500000 : ℝ)^8273 ≤ (51102050410007/100000000000000 : ℝ)^6225 := by
    have hnat : (37713349 : ℕ)^8273*100000000000000^6225 ≤ 51102050410007^6225*62500000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37713349 62500000 51102050410007 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239615093/1250000000 : ℝ), (961208957/2000000000 : ℝ), (37713349/62500000 : ℝ)] ![(1113227191879/10000000000000 : ℝ), (37765677662977/100000000000000 : ℝ), (51102050410007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239615093/1250000000 : ℝ)|^8273 ≤ (1113227191879/10000000000000 : ℝ)^6225
        have hw : |(-239615093/1250000000 : ℝ)|=(239615093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(961208957/2000000000 : ℝ)|^8273 ≤ (37765677662977/100000000000000 : ℝ)^6225
        have hw : |(961208957/2000000000 : ℝ)|=(961208957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37713349/62500000 : ℝ)|^8273 ≤ (51102050410007/100000000000000 : ℝ)^6225
        have hw : |(37713349/62500000 : ℝ)|=(37713349/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s0_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292100649/2500000000 : ℝ)*x 0 + (-139571713/1000000000 : ℝ)*x 1 + (1206826801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292100649/2500000000 : ℝ)^8273 ≤ (41596014569933/100000000000000 : ℝ)^6225 := by
    have hnat : (1292100649 : ℕ)^8273*100000000000000^6225 ≤ 41596014569933^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292100649 2500000000 41596014569933 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139571713/1000000000 : ℝ)^8273 ≤ (3650977824353/50000000000000 : ℝ)^6225 := by
    have hnat : (139571713 : ℕ)^8273*50000000000000^6225 ≤ 3650977824353^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139571713 1000000000 3650977824353 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206826801/2000000000 : ℝ)^8273 ≤ (10220405951403/20000000000000 : ℝ)^6225 := by
    have hnat : (1206826801 : ℕ)^8273*20000000000000^6225 ≤ 10220405951403^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206826801 2000000000 10220405951403 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292100649/2500000000 : ℝ), (-139571713/1000000000 : ℝ), (1206826801/2000000000 : ℝ)] ![(41596014569933/100000000000000 : ℝ), (3650977824353/50000000000000 : ℝ), (10220405951403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292100649/2500000000 : ℝ)|^8273 ≤ (41596014569933/100000000000000 : ℝ)^6225
        have hw : |(1292100649/2500000000 : ℝ)|=(1292100649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139571713/1000000000 : ℝ)|^8273 ≤ (3650977824353/50000000000000 : ℝ)^6225
        have hw : |(-139571713/1000000000 : ℝ)|=(139571713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206826801/2000000000 : ℝ)|^8273 ≤ (10220405951403/20000000000000 : ℝ)^6225
        have hw : |(1206826801/2000000000 : ℝ)|=(1206826801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s0_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584201267/5000000000 : ℝ)*x 0 + (1206827099/2000000000 : ℝ)*x 1 + (-697857407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584201267/5000000000 : ℝ)^8273 ≤ (8319202781357/20000000000000 : ℝ)^6225 := by
    have hnat : (2584201267 : ℕ)^8273*20000000000000^6225 ≤ 8319202781357^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584201267 5000000000 8319202781357 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206827099/2000000000 : ℝ)^8273 ≤ (51102046527019/100000000000000 : ℝ)^6225 := by
    have hnat : (1206827099 : ℕ)^8273*100000000000000^6225 ≤ 51102046527019^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206827099 2000000000 51102046527019 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (697857407/5000000000 : ℝ)^8273 ≤ (3650969772907/50000000000000 : ℝ)^6225 := by
    have hnat : (697857407 : ℕ)^8273*50000000000000^6225 ≤ 3650969772907^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697857407 5000000000 3650969772907 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584201267/5000000000 : ℝ), (1206827099/2000000000 : ℝ), (-697857407/5000000000 : ℝ)] ![(8319202781357/20000000000000 : ℝ), (51102046527019/100000000000000 : ℝ), (3650969772907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584201267/5000000000 : ℝ)|^8273 ≤ (8319202781357/20000000000000 : ℝ)^6225
        have hw : |(2584201267/5000000000 : ℝ)|=(2584201267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206827099/2000000000 : ℝ)|^8273 ≤ (51102046527019/100000000000000 : ℝ)^6225
        have hw : |(1206827099/2000000000 : ℝ)|=(1206827099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-697857407/5000000000 : ℝ)|^8273 ≤ (3650969772907/50000000000000 : ℝ)^6225
        have hw : |(-697857407/5000000000 : ℝ)|=(697857407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s0_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2108264063/5000000000 : ℝ)*x 0 + (2802886823/5000000000 : ℝ)*x 1 + (127687971/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108264063/5000000000 : ℝ)^8273 ≤ (31737060762061/100000000000000 : ℝ)^6225 := by
    have hnat : (2108264063 : ℕ)^8273*100000000000000^6225 ≤ 31737060762061^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108264063 5000000000 31737060762061 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2802886823/5000000000 : ℝ)^8273 ≤ (11584510142057/25000000000000 : ℝ)^6225 := by
    have hnat : (2802886823 : ℕ)^8273*25000000000000^6225 ≤ 11584510142057^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802886823 5000000000 11584510142057 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127687971/400000000 : ℝ)^8273 ≤ (10962449324719/50000000000000 : ℝ)^6225 := by
    have hnat : (127687971 : ℕ)^8273*50000000000000^6225 ≤ 10962449324719^6225*400000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127687971 400000000 10962449324719 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2108264063/5000000000 : ℝ), (2802886823/5000000000 : ℝ), (127687971/400000000 : ℝ)] ![(31737060762061/100000000000000 : ℝ), (11584510142057/25000000000000 : ℝ), (10962449324719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2108264063/5000000000 : ℝ)|^8273 ≤ (31737060762061/100000000000000 : ℝ)^6225
        have hw : |(2108264063/5000000000 : ℝ)|=(2108264063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2802886823/5000000000 : ℝ)|^8273 ≤ (11584510142057/25000000000000 : ℝ)^6225
        have hw : |(2802886823/5000000000 : ℝ)|=(2802886823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127687971/400000000 : ℝ)|^8273 ≤ (10962449324719/50000000000000 : ℝ)^6225
        have hw : |(127687971/400000000 : ℝ)|=(127687971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (39/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5611/20000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base34 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1, f.sum]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (517/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^517 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^517*1^128 ≤ 0^128*1^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (517/128 : ℝ) ≤ (617497839456341027/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^517 ≤ (617497839456341027/25000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^517*25000000000000000000^128 ≤ 617497839456341027^128*5^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 617497839456341027 25000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (617497839456341027/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^517 := by
      have hnat : (1 : ℕ)^128*1^517 ≤ 1^517*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25617497839456341027/25000000000000000000 : ℝ) ≤ (2515148100698659/2500000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (25617497839456341027/25000000000000000000 : ℝ)^128 ≤ (2515148100698659/2500000000000000 : ℝ)^517 := by
      have hnat : (25617497839456341027 : ℕ)^128*2500000000000000^517 ≤ 2515148100698659^517*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25617497839456341027 25000000000000000000 2515148100698659 2500000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515148100698659/2500000000000000 : ℝ)) (X := (25617497839456341027/25000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (13117497839456341027/12500000000000000000 : ℝ) ≤ (1265148100698659/1250000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (13117497839456341027/12500000000000000000 : ℝ)^128 ≤ (1265148100698659/1250000000000000 : ℝ)^517 := by
      have hnat : (13117497839456341027 : ℕ)^128*1250000000000000^517 ≤ 1265148100698659^517*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13117497839456341027 12500000000000000000 1265148100698659 1250000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265148100698659/1250000000000000 : ℝ)) (X := (13117497839456341027/12500000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15148100698659/1000000000000000 : ℝ)*(0 : ℝ))^(517/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(15148100698659/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(617497839456341027/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15148100698659/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(517/128 : ℝ) := by
    rw [show (1 : ℝ)+(15148100698659/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2515148100698659/2500000000000000 : ℝ) by norm_num, show 1+(617497839456341027/25000000000000000000 : ℝ)+(0 : ℝ)=(25617497839456341027/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(617497839456341027/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15148100698659/1000000000000000 : ℝ)*(2/5 : ℝ))^(517/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(15148100698659/1000000000000000 : ℝ)*(2/5 : ℝ)=(1265148100698659/1250000000000000 : ℝ) by norm_num, show 1+2*(617497839456341027/25000000000000000000 : ℝ)=(13117497839456341027/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15148100698659/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15148100698659/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15148100698659/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15148100698659/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15148100698659/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15148100698659/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-477897587/2500000000 : ℝ)*X 0 0+(6068771331/10000000000 : ℝ)*X 0 1+(2386290377/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((690035533/1250000000 : ℝ)*X 1 0+(-664317403/2500000000 : ℝ)*X 1 1+(954516237/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((138007119/250000000 : ℝ)*X 2 0+(4772581613/10000000000 : ℝ)*X 2 1+(-1328634231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2103026393/5000000000 : ℝ)*X 0 0+(312412861/1000000000 : ℝ)*X 0 1+(708942717/1250000000 : ℝ)*X 0 2+(2103026393/5000000000 : ℝ)*X 1 0+(312412861/1000000000 : ℝ)*X 1 1+(708942717/1250000000 : ℝ)*X 1 2+(2103026393/5000000000 : ℝ)*X 2 0+(312412861/1000000000 : ℝ)*X 2 1+(708942717/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-239615093/1250000000 : ℝ)*X 0 0+(961208957/2000000000 : ℝ)*X 0 1+(37713349/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1292100649/2500000000 : ℝ)*X 1 0+(-139571713/1000000000 : ℝ)*X 1 1+(1206826801/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584201267/5000000000 : ℝ)*X 2 0+(1206827099/2000000000 : ℝ)*X 2 1+(-697857407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2108264063/5000000000 : ℝ)*X 0 0+(2802886823/5000000000 : ℝ)*X 0 1+(127687971/400000000 : ℝ)*X 0 2+(2108264063/5000000000 : ℝ)*X 1 0+(2802886823/5000000000 : ℝ)*X 1 1+(127687971/400000000 : ℝ)*X 1 2+(2108264063/5000000000 : ℝ)*X 2 0+(2802886823/5000000000 : ℝ)*X 2 1+(127687971/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64978801423975965345381/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133515913/100000000000000 : ℝ)*(base19) + (53163381/50000000000000 : ℝ)*(base23) + (32929523/25000000000000 : ℝ)*(base24) + (47865933/50000000000000 : ℝ)*(base34) + (131935331/100000000000000 : ℝ)*(base39) + (9205271/6250000000000 : ℝ)*(upper3) + (116404805215219/20000000000000 : ℝ)*(major0) + (58202393034423/10000000000000 : ℝ)*(major1) + (145505973535191/25000000000000 : ℝ)*(major2) + (154298483158553/20000000000000 : ℝ)*(sp0) + (771492378008717/100000000000000 : ℝ)*(sp1) + (385746154841621/50000000000000 : ℝ)*(sp2) + (49069372561583/12500000000000 : ℝ)*(sp3) + (96220089/25000000000000 : ℝ)*(sp7) + (392555365373019/100000000000000 : ℝ)*(f.failure) + (771492643459961/100000000000000 : ℝ)*(f.sum) + (134011996288477/50000000000000000000000000000 : ℝ)*base66 + (12614657766131/25000000000000000000000000000 : ℝ)*base68 + (21180777201243/10000000000000000000000000000 : ℝ)*base70 + (50213378191131/25000000000000000000000000000 : ℝ)*base72 + (369312030707919/100000000000000000000000000000 : ℝ)*base74 + (148718365288679/20000000000000000000000000000 : ℝ)*base76 + (56525129861243/10000000000000000000000000000 : ℝ)*base78 + (49236127548679/20000000000000000000000000000 : ℝ)*base80 + (24547675513767/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (17815111/5000000000000000000000 : ℝ)*base90 + (67815111/5000000000000000000000 : ℝ)*base92 + (17815111/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (439869074550489250204659/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1919047933/100000000000000 : ℝ)*(base19) + (2087088487/100000000000000 : ℝ)*(base23) + (119682003/100000000000000 : ℝ)*(base39) + (415352523/100000000000000 : ℝ)*(base45) + (1533577/781250000000 : ℝ)*(upper3) + (372321087/100000000000000 : ℝ)*(upper5) + (614295149023113/100000000000000 : ℝ)*(major0) + (614295149023113/100000000000000 : ℝ)*(major1) + (61429502934111/10000000000000 : ℝ)*(major2) + (56579753/6250000000000 : ℝ)*(sp2) + (101783593423177/12500000000000 : ℝ)*(sp4) + (407133414168741/50000000000000 : ℝ)*(sp5) + (814265874702883/100000000000000 : ℝ)*(sp6) + (207160568866373/50000000000000 : ℝ)*(sp7) + (207160568866373/50000000000000 : ℝ)*(f.failure) + (814268867067419/100000000000000 : ℝ)*(f.sum) + (303177620476957/100000000000000000000000000000 : ℝ)*base65 + (75230868297149/10000000000000000000000000000 : ℝ)*base67 + (537830219894533/100000000000000000000000000000 : ℝ)*base70 + (64798370377149/10000000000000000000000000000 : ℝ)*base71 + (604897544076957/100000000000000000000000000000 : ℝ)*base73 + (184833183105467/100000000000000000000000000000 : ℝ)*base75 + (678361839305467/100000000000000000000000000000 : ℝ)*base77 + (854431696605467/100000000000000000000000000000 : ℝ)*base79 + (323390971494533/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (20445337/2500000000000000000000 : ℝ)*base90 + (20445337/2500000000000000000000 : ℝ)*base92 + (20445337/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1080_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (39/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5611/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1080_s1_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120713529/10000000000 : ℝ)*x 0 + (5718417701/10000000000 : ℝ)*x 1 + (4989020981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120713529/10000000000 : ℝ)^8273 ≤ (127320194129/1000000000000 : ℝ)^6225 := by
    have hnat : (2120713529 : ℕ)^8273*1000000000000^6225 ≤ 127320194129^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120713529 10000000000 127320194129 1000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5718417701/10000000000 : ℝ)^8273 ≤ (9515916193217/20000000000000 : ℝ)^6225 := by
    have hnat : (5718417701 : ℕ)^8273*20000000000000^6225 ≤ 9515916193217^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5718417701 10000000000 9515916193217 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4989020981/10000000000 : ℝ)^8273 ≤ (39688399608819/100000000000000 : ℝ)^6225 := by
    have hnat : (4989020981 : ℕ)^8273*100000000000000^6225 ≤ 39688399608819^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989020981 10000000000 39688399608819 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120713529/10000000000 : ℝ), (5718417701/10000000000 : ℝ), (4989020981/10000000000 : ℝ)] ![(127320194129/1000000000000 : ℝ), (9515916193217/20000000000000 : ℝ), (39688399608819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120713529/10000000000 : ℝ)|^8273 ≤ (127320194129/1000000000000 : ℝ)^6225
        have hw : |(-2120713529/10000000000 : ℝ)|=(2120713529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5718417701/10000000000 : ℝ)|^8273 ≤ (9515916193217/20000000000000 : ℝ)^6225
        have hw : |(5718417701/10000000000 : ℝ)|=(5718417701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4989020981/10000000000 : ℝ)|^8273 ≤ (39688399608819/100000000000000 : ℝ)^6225
        have hw : |(4989020981/10000000000 : ℝ)|=(4989020981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s1_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711270709/5000000000 : ℝ)*x 0 + (-31445083/125000000 : ℝ)*x 1 + (4989021259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711270709/5000000000 : ℝ)^8273 ≤ (44336018757203/100000000000000 : ℝ)^6225 := by
    have hnat : (2711270709 : ℕ)^8273*100000000000000^6225 ≤ 44336018757203^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711270709 5000000000 44336018757203 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31445083/125000000 : ℝ)^8273 ≤ (124809208417/781250000000 : ℝ)^6225 := by
    have hnat : (31445083 : ℕ)^8273*781250000000^6225 ≤ 124809208417^6225*125000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31445083 125000000 124809208417 781250000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4989021259/10000000000 : ℝ)^8273 ≤ (7937680509587/20000000000000 : ℝ)^6225 := by
    have hnat : (4989021259 : ℕ)^8273*20000000000000^6225 ≤ 7937680509587^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989021259 10000000000 7937680509587 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711270709/5000000000 : ℝ), (-31445083/125000000 : ℝ), (4989021259/10000000000 : ℝ)] ![(44336018757203/100000000000000 : ℝ), (124809208417/781250000000 : ℝ), (7937680509587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711270709/5000000000 : ℝ)|^8273 ≤ (44336018757203/100000000000000 : ℝ)^6225
        have hw : |(2711270709/5000000000 : ℝ)|=(2711270709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31445083/125000000 : ℝ)|^8273 ≤ (124809208417/781250000000 : ℝ)^6225
        have hw : |(-31445083/125000000 : ℝ)|=(31445083/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4989021259/10000000000 : ℝ)|^8273 ≤ (7937680509587/20000000000000 : ℝ)^6225
        have hw : |(4989021259/10000000000 : ℝ)|=(4989021259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s1_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67781777/125000000 : ℝ)*x 0 + (2494510233/5000000000 : ℝ)*x 1 + (-2515606679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67781777/125000000 : ℝ)^8273 ≤ (44336026819919/100000000000000 : ℝ)^6225 := by
    have hnat : (67781777 : ℕ)^8273*100000000000000^6225 ≤ 44336026819919^6225*125000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67781777 125000000 44336026819919 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2494510233/5000000000 : ℝ)^8273 ≤ (19844197082027/50000000000000 : ℝ)^6225 := by
    have hnat : (2494510233 : ℕ)^8273*50000000000000^6225 ≤ 19844197082027^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494510233 5000000000 19844197082027 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2515606679/10000000000 : ℝ)^8273 ≤ (15975579006533/100000000000000 : ℝ)^6225 := by
    have hnat : (2515606679 : ℕ)^8273*100000000000000^6225 ≤ 15975579006533^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515606679 10000000000 15975579006533 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67781777/125000000 : ℝ), (2494510233/5000000000 : ℝ), (-2515606679/10000000000 : ℝ)] ![(44336026819919/100000000000000 : ℝ), (19844197082027/50000000000000 : ℝ), (15975579006533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67781777/125000000 : ℝ)|^8273 ≤ (44336026819919/100000000000000 : ℝ)^6225
        have hw : |(67781777/125000000 : ℝ)|=(67781777/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2494510233/5000000000 : ℝ)|^8273 ≤ (19844197082027/50000000000000 : ℝ)^6225
        have hw : |(2494510233/5000000000 : ℝ)|=(2494510233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2515606679/10000000000 : ℝ)|^8273 ≤ (15975579006533/100000000000000 : ℝ)^6225
        have hw : |(-2515606679/10000000000 : ℝ)|=(2515606679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s1_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4322639983/10000000000 : ℝ)*x 0 + (3665237009/10000000000 : ℝ)*x 1 + (5098725681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322639983/10000000000 : ℝ)^8273 ≤ (16401439873893/50000000000000 : ℝ)^6225 := by
    have hnat : (4322639983 : ℕ)^8273*50000000000000^6225 ≤ 16401439873893^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322639983 10000000000 16401439873893 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665237009/10000000000 : ℝ)^8273 ≤ (411636065517/1562500000000 : ℝ)^6225 := by
    have hnat : (3665237009 : ℕ)^8273*1562500000000^6225 ≤ 411636065517^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665237009 10000000000 411636065517 1562500000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098725681/10000000000 : ℝ)^8273 ≤ (40852412041481/100000000000000 : ℝ)^6225 := by
    have hnat : (5098725681 : ℕ)^8273*100000000000000^6225 ≤ 40852412041481^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098725681 10000000000 40852412041481 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322639983/10000000000 : ℝ), (3665237009/10000000000 : ℝ), (5098725681/10000000000 : ℝ)] ![(16401439873893/50000000000000 : ℝ), (411636065517/1562500000000 : ℝ), (40852412041481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322639983/10000000000 : ℝ)|^8273 ≤ (16401439873893/50000000000000 : ℝ)^6225
        have hw : |(4322639983/10000000000 : ℝ)|=(4322639983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3665237009/10000000000 : ℝ)|^8273 ≤ (411636065517/1562500000000 : ℝ)^6225
        have hw : |(3665237009/10000000000 : ℝ)|=(3665237009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098725681/10000000000 : ℝ)|^8273 ≤ (40852412041481/100000000000000 : ℝ)^6225
        have hw : |(5098725681/10000000000 : ℝ)|=(5098725681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s1_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-424322111/2000000000 : ℝ)*x 0 + (2499609201/5000000000 : ℝ)*x 1 + (22832057/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424322111/2000000000 : ℝ)^8273 ≤ (3184794281139/25000000000000 : ℝ)^6225 := by
    have hnat : (424322111 : ℕ)^8273*25000000000000^6225 ≤ 3184794281139^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424322111 2000000000 3184794281139 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2499609201/5000000000 : ℝ)^8273 ≤ (7959249328573/20000000000000 : ℝ)^6225 := by
    have hnat : (2499609201 : ℕ)^8273*20000000000000^6225 ≤ 7959249328573^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499609201 5000000000 7959249328573 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22832057/40000000 : ℝ)^8273 ≤ (9492915242653/20000000000000 : ℝ)^6225 := by
    have hnat : (22832057 : ℕ)^8273*20000000000000^6225 ≤ 9492915242653^6225*40000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22832057 40000000 9492915242653 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424322111/2000000000 : ℝ), (2499609201/5000000000 : ℝ), (22832057/40000000 : ℝ)] ![(3184794281139/25000000000000 : ℝ), (7959249328573/20000000000000 : ℝ), (9492915242653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424322111/2000000000 : ℝ)|^8273 ≤ (3184794281139/25000000000000 : ℝ)^6225
        have hw : |(-424322111/2000000000 : ℝ)|=(424322111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2499609201/5000000000 : ℝ)|^8273 ≤ (7959249328573/20000000000000 : ℝ)^6225
        have hw : |(2499609201/5000000000 : ℝ)|=(2499609201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22832057/40000000 : ℝ)|^8273 ≤ (9492915242653/20000000000000 : ℝ)^6225
        have hw : |(22832057/40000000 : ℝ)|=(22832057/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s1_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2618063959/5000000000 : ℝ)*x 0 + (-1796613459/10000000000 : ℝ)*x 1 + (2854007053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618063959/5000000000 : ℝ)^8273 ≤ (8464391520027/20000000000000 : ℝ)^6225 := by
    have hnat : (2618063959 : ℕ)^8273*20000000000000^6225 ≤ 8464391520027^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618063959 5000000000 8464391520027 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1796613459/10000000000 : ℝ)^8273 ≤ (1021346776167/10000000000000 : ℝ)^6225 := by
    have hnat : (1796613459 : ℕ)^8273*10000000000000^6225 ≤ 1021346776167^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796613459 10000000000 1021346776167 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2854007053/5000000000 : ℝ)^8273 ≤ (47464574621897/100000000000000 : ℝ)^6225 := by
    have hnat : (2854007053 : ℕ)^8273*100000000000000^6225 ≤ 47464574621897^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854007053 5000000000 47464574621897 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618063959/5000000000 : ℝ), (-1796613459/10000000000 : ℝ), (2854007053/5000000000 : ℝ)] ![(8464391520027/20000000000000 : ℝ), (1021346776167/10000000000000 : ℝ), (47464574621897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618063959/5000000000 : ℝ)|^8273 ≤ (8464391520027/20000000000000 : ℝ)^6225
        have hw : |(2618063959/5000000000 : ℝ)|=(2618063959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1796613459/10000000000 : ℝ)|^8273 ≤ (1021346776167/10000000000000 : ℝ)^6225
        have hw : |(-1796613459/10000000000 : ℝ)|=(1796613459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2854007053/5000000000 : ℝ)|^8273 ≤ (47464574621897/100000000000000 : ℝ)^6225
        have hw : |(2854007053/5000000000 : ℝ)|=(2854007053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s1_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2618063967/5000000000 : ℝ)*x 0 + (2854007109/5000000000 : ℝ)*x 1 + (-224576659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618063967/5000000000 : ℝ)^8273 ≤ (8464391554401/20000000000000 : ℝ)^6225 := by
    have hnat : (2618063967 : ℕ)^8273*20000000000000^6225 ≤ 8464391554401^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618063967 5000000000 8464391554401 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2854007109/5000000000 : ℝ)^8273 ≤ (11866143964907/25000000000000 : ℝ)^6225 := by
    have hnat : (2854007109 : ℕ)^8273*25000000000000^6225 ≤ 11866143964907^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854007109 5000000000 11866143964907 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224576659/1250000000 : ℝ)^8273 ≤ (10213466348859/100000000000000 : ℝ)^6225 := by
    have hnat : (224576659 : ℕ)^8273*100000000000000^6225 ≤ 10213466348859^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224576659 1250000000 10213466348859 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618063967/5000000000 : ℝ), (2854007109/5000000000 : ℝ), (-224576659/1250000000 : ℝ)] ![(8464391554401/20000000000000 : ℝ), (11866143964907/25000000000000 : ℝ), (10213466348859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618063967/5000000000 : ℝ)|^8273 ≤ (8464391554401/20000000000000 : ℝ)^6225
        have hw : |(2618063967/5000000000 : ℝ)|=(2618063967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2854007109/5000000000 : ℝ)|^8273 ≤ (11866143964907/25000000000000 : ℝ)^6225
        have hw : |(2854007109/5000000000 : ℝ)|=(2854007109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224576659/1250000000 : ℝ)|^8273 ≤ (10213466348859/100000000000000 : ℝ)^6225
        have hw : |(-224576659/1250000000 : ℝ)|=(224576659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s1_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (864880463/2000000000 : ℝ)*x 0 + (634835673/1250000000 : ℝ)*x 1 + (3685682329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864880463/2000000000 : ℝ)^8273 ≤ (1025645452957/3125000000000 : ℝ)^6225 := by
    have hnat : (864880463 : ℕ)^8273*3125000000000^6225 ≤ 1025645452957^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864880463 2000000000 1025645452957 3125000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634835673/1250000000 : ℝ)^8273 ≤ (8127831062177/20000000000000 : ℝ)^6225 := by
    have hnat : (634835673 : ℕ)^8273*20000000000000^6225 ≤ 8127831062177^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634835673 1250000000 8127831062177 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3685682329/10000000000 : ℝ)^8273 ≤ (13270095088881/50000000000000 : ℝ)^6225 := by
    have hnat : (3685682329 : ℕ)^8273*50000000000000^6225 ≤ 13270095088881^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685682329 10000000000 13270095088881 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864880463/2000000000 : ℝ), (634835673/1250000000 : ℝ), (3685682329/10000000000 : ℝ)] ![(1025645452957/3125000000000 : ℝ), (8127831062177/20000000000000 : ℝ), (13270095088881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864880463/2000000000 : ℝ)|^8273 ≤ (1025645452957/3125000000000 : ℝ)^6225
        have hw : |(864880463/2000000000 : ℝ)|=(864880463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(634835673/1250000000 : ℝ)|^8273 ≤ (8127831062177/20000000000000 : ℝ)^6225
        have hw : |(634835673/1250000000 : ℝ)|=(634835673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3685682329/10000000000 : ℝ)|^8273 ≤ (13270095088881/50000000000000 : ℝ)^6225
        have hw : |(3685682329/10000000000 : ℝ)|=(3685682329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5611/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (39/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1059/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5181/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5611/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (39/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5611/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (39/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5611/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (39/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5611/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (39/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5611/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (39/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5611/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (39/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (39/25000 : ℝ) ^ (517/128 : ℝ) ≤ (57512843/12500000000000000000 : ℝ) := by
    have hpowers : (39/25000 : ℝ)^517 ≤ (57512843/12500000000000000000 : ℝ)^128 := by
      have hnat : (39 : ℕ)^517*12500000000000000000^128 ≤ 57512843^128*25000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39 25000 57512843 12500000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39/25000 : ℝ)) (X := (57512843/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (5611/20000 : ℝ) ^ (517/128 : ℝ) ≤ (589493462947102789/100000000000000000000 : ℝ) := by
    have hpowers : (5611/20000 : ℝ)^517 ≤ (589493462947102789/100000000000000000000 : ℝ)^128 := by
      have hnat : (5611 : ℕ)^517*100000000000000000000^128 ≤ 589493462947102789^128*20000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5611 20000 589493462947102789 100000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5611/20000 : ℝ)) (X := (589493462947102789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000000057512843/6250000000000000000 : ℝ) ≤ (10000000000022783/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (6250000000057512843/6250000000000000000 : ℝ)^128 ≤ (10000000000022783/10000000000000000 : ℝ)^517 := by
      have hnat : (6250000000057512843 : ℕ)^128*10000000000000000^517 ≤ 10000000000022783^517*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000000057512843 6250000000000000000 10000000000022783 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000022783/10000000000000000 : ℝ)) (X := (6250000000057512843/6250000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100589493463407205533/100000000000000000000 : ℝ) ≤ (5007281276428637/5000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (100589493463407205533/100000000000000000000 : ℝ)^128 ≤ (5007281276428637/5000000000000000 : ℝ)^517 := by
      have hnat : (100589493463407205533 : ℕ)^128*5000000000000000^517 ≤ 5007281276428637^517*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100589493463407205533 100000000000000000000 5007281276428637 5000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007281276428637/5000000000000000 : ℝ)) (X := (100589493463407205533/100000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50589493462947102789/50000000000000000000 : ℝ) ≤ (2005825021138353/2000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50589493462947102789/50000000000000000000 : ℝ)^128 ≤ (2005825021138353/2000000000000000 : ℝ)^517 := by
      have hnat : (50589493462947102789 : ℕ)^128*2000000000000000^517 ≤ 2005825021138353^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50589493462947102789 50000000000000000000 2005825021138353 2000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005825021138353/2000000000000000 : ℝ)) (X := (50589493462947102789/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(57512843/12500000000000000000 : ℝ) ≤ ((11159418259366050469/11159600000000000000 : ℝ)+2*(14562552834491/2789900000000000 : ℝ)*(39/25000 : ℝ))^(517/128 : ℝ) := by
    rw [show (11159418259366050469/11159600000000000000 : ℝ)+2*(14562552834491/2789900000000000 : ℝ)*(39/25000 : ℝ)=(10000000000022783/10000000000000000 : ℝ) by norm_num, show 1+2*(57512843/12500000000000000000 : ℝ)=(6250000000057512843/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(589493462947102789/100000000000000000000 : ℝ)+(57512843/12500000000000000000 : ℝ) ≤ ((11159418259366050469/11159600000000000000 : ℝ)+(14562552834491/2789900000000000 : ℝ)*((5611/20000 : ℝ)+(39/25000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (11159418259366050469/11159600000000000000 : ℝ)+(14562552834491/2789900000000000 : ℝ)*((5611/20000 : ℝ)+(39/25000 : ℝ))=(5007281276428637/5000000000000000 : ℝ) by norm_num, show 1+(589493462947102789/100000000000000000000 : ℝ)+(57512843/12500000000000000000 : ℝ)=(100589493463407205533/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(589493462947102789/100000000000000000000 : ℝ) ≤ ((11159418259366050469/11159600000000000000 : ℝ)+2*(14562552834491/2789900000000000 : ℝ)*(5611/20000 : ℝ))^(517/128 : ℝ) := by
    rw [show (11159418259366050469/11159600000000000000 : ℝ)+2*(14562552834491/2789900000000000 : ℝ)*(5611/20000 : ℝ)=(2005825021138353/2000000000000000 : ℝ) by norm_num, show 1+2*(589493462947102789/100000000000000000000 : ℝ)=(50589493462947102789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11159418259366050469/11159600000000000000 : ℝ)*(X 1 0+X 2 0)+(14562552834491/2789900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (39/25000 : ℝ)) (hi := (5611/20000 : ℝ)) (c := (11159418259366050469/11159600000000000000 : ℝ)) (alpha := (14562552834491/2789900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11159418259366050469/11159600000000000000 : ℝ)*(X 0 1+X 2 1)+(14562552834491/2789900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (39/25000 : ℝ)) (hi := (5611/20000 : ℝ)) (c := (11159418259366050469/11159600000000000000 : ℝ)) (alpha := (14562552834491/2789900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11159418259366050469/11159600000000000000 : ℝ)*(X 0 2+X 1 2)+(14562552834491/2789900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (39/25000 : ℝ)) (hi := (5611/20000 : ℝ)) (c := (11159418259366050469/11159600000000000000 : ℝ)) (alpha := (14562552834491/2789900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2120713529/10000000000 : ℝ)*X 0 0+(5718417701/10000000000 : ℝ)*X 0 1+(4989020981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711270709/5000000000 : ℝ)*X 1 0+(-31445083/125000000 : ℝ)*X 1 1+(4989021259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((67781777/125000000 : ℝ)*X 2 0+(2494510233/5000000000 : ℝ)*X 2 1+(-2515606679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322639983/10000000000 : ℝ)*X 0 0+(3665237009/10000000000 : ℝ)*X 0 1+(5098725681/10000000000 : ℝ)*X 0 2+(4322639983/10000000000 : ℝ)*X 1 0+(3665237009/10000000000 : ℝ)*X 1 1+(5098725681/10000000000 : ℝ)*X 1 2+(4322639983/10000000000 : ℝ)*X 2 0+(3665237009/10000000000 : ℝ)*X 2 1+(5098725681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-424322111/2000000000 : ℝ)*X 0 0+(2499609201/5000000000 : ℝ)*X 0 1+(22832057/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2618063959/5000000000 : ℝ)*X 1 0+(-1796613459/10000000000 : ℝ)*X 1 1+(2854007053/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2618063967/5000000000 : ℝ)*X 2 0+(2854007109/5000000000 : ℝ)*X 2 1+(-224576659/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864880463/2000000000 : ℝ)*X 0 0+(634835673/1250000000 : ℝ)*X 0 1+(3685682329/10000000000 : ℝ)*X 0 2+(864880463/2000000000 : ℝ)*X 1 0+(634835673/1250000000 : ℝ)*X 1 1+(3685682329/10000000000 : ℝ)*X 1 2+(864880463/2000000000 : ℝ)*X 2 0+(634835673/1250000000 : ℝ)*X 2 1+(3685682329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3516091367798120966970972561/557980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34954207/25000000000000 : ℝ)*(base1) + (1314431681/100000000000000 : ℝ)*(base19) + (1502035153/100000000000000 : ℝ)*(base23) + (120920283/100000000000000 : ℝ)*(upper3) + (39658637/25000000000000 : ℝ)*(upper5) + (1034307048402623/100000000000000 : ℝ)*(major0) + (1034307048402623/100000000000000 : ℝ)*(major1) + (1034307048402623/100000000000000 : ℝ)*(major2) + (5355477114167/390625000000 : ℝ)*(sp0) + (1371007725956247/100000000000000 : ℝ)*(sp1) + (171375942294097/12500000000000 : ℝ)*(sp2) + (174400426087311/25000000000000 : ℝ)*(sp3) + (1407795601/20000000000000 : ℝ)*(sp4) + (3002202411/100000000000000 : ℝ)*(sp7) + (174401211592121/25000000000000 : ℝ)*(f.failure) + (171376130048491/12500000000000 : ℝ)*(f.sum) + (99745809545563/139495000000000000000000000000 : ℝ)*base65 + (4756267054495167813/1115960000000000000000000000000000 : ℝ)*base68 + (2657333957676647813/1115960000000000000000000000000000 : ℝ)*base70 + (315890538675927813/1115960000000000000000000000000000 : ℝ)*base72 + (559970433600407/139495000000000000000000000000 : ℝ)*base74 + (4480569382047792187/1115960000000000000000000000000000 : ℝ)*base75 + (2324281422783367813/1115960000000000000000000000000000 : ℝ)*base78 + (788794835978992187/1115960000000000000000000000000000 : ℝ)*base79 + (52574144713303/34873750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (312451/1250000000000000000000 : ℝ)*base89 + (312451/1250000000000000000000 : ℝ)*base91 + (312451/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25693237870888778996783199/13949500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26091843/100000000000000 : ℝ)*(base1) + (217109503/50000000000000 : ℝ)*(base19) + (451709369/100000000000000 : ℝ)*(base23) + (39343237/100000000000000 : ℝ)*(upper3) + (19394699/50000000000000 : ℝ)*(upper5) + (53217927983443/5000000000000 : ℝ)*(major0) + (53217927983443/5000000000000 : ℝ)*(major1) + (53217927983443/5000000000000 : ℝ)*(major2) + (1555141217/100000000000000 : ℝ)*(sp1) + (962661521/50000000000000 : ℝ)*(sp2) + (282168703544277/20000000000000 : ℝ)*(sp4) + (1410841502269319/100000000000000 : ℝ)*(sp5) + (1410841114597131/100000000000000 : ℝ)*(sp6) + (179468385055123/25000000000000 : ℝ)*(sp7) + (143574713262467/20000000000000 : ℝ)*(f.failure) + (705421745814771/50000000000000 : ℝ)*(f.sum) + (35915152840857/27899000000000000000000000000 : ℝ)*base65 + (288334208147432767/55798000000000000000000000000000 : ℝ)*base67 + (85161222675727233/55798000000000000000000000000000 : ℝ)*base70 + (45484749627092767/55798000000000000000000000000000 : ℝ)*base71 + (79810788780379/27899000000000000000000000000 : ℝ)*base73 + (299096739145206767/55798000000000000000000000000000 : ℝ)*base75 + (153864858345344767/55798000000000000000000000000000 : ℝ)*base77 + (272238752778152767/55798000000000000000000000000000 : ℝ)*base79 + (9528116163643/2789900000000000000000000000 : ℝ)*base82 + (1492623/1000000000000000000000 : ℝ)*base90 + (1492623/1000000000000000000000 : ℝ)*base92 + (1492623/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1080_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5611/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (39/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1059/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5181/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1080_s2_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177355643/10000000000 : ℝ)*x 0 + (5523021499/10000000000 : ℝ)*x 1 + (1287116279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177355643/10000000000 : ℝ)^8273 ≤ (2637186166523/20000000000000 : ℝ)^6225 := by
    have hnat : (2177355643 : ℕ)^8273*20000000000000^6225 ≤ 2637186166523^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177355643 10000000000 2637186166523 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5523021499/10000000000 : ℝ)^8273 ≤ (22715584642381/50000000000000 : ℝ)^6225 := by
    have hnat : (5523021499 : ℕ)^8273*50000000000000^6225 ≤ 22715584642381^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523021499 10000000000 22715584642381 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287116279/2500000000 : ℝ)^8273 ≤ (41382899870377/100000000000000 : ℝ)^6225 := by
    have hnat : (1287116279 : ℕ)^8273*100000000000000^6225 ≤ 41382899870377^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287116279 2500000000 41382899870377 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177355643/10000000000 : ℝ), (5523021499/10000000000 : ℝ), (1287116279/2500000000 : ℝ)] ![(2637186166523/20000000000000 : ℝ), (22715584642381/50000000000000 : ℝ), (41382899870377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177355643/10000000000 : ℝ)|^8273 ≤ (2637186166523/20000000000000 : ℝ)^6225
        have hw : |(-2177355643/10000000000 : ℝ)|=(2177355643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5523021499/10000000000 : ℝ)|^8273 ≤ (22715584642381/50000000000000 : ℝ)^6225
        have hw : |(5523021499/10000000000 : ℝ)|=(5523021499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287116279/2500000000 : ℝ)|^8273 ≤ (41382899870377/100000000000000 : ℝ)^6225
        have hw : |(1287116279/2500000000 : ℝ)|=(1287116279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s2_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1344143793/2500000000 : ℝ)*x 0 + (-118628831/500000000 : ℝ)*x 1 + (643558201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344143793/2500000000 : ℝ)^8273 ≤ (43837238390739/100000000000000 : ℝ)^6225 := by
    have hnat : (1344143793 : ℕ)^8273*100000000000000^6225 ≤ 43837238390739^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344143793 2500000000 43837238390739 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118628831/500000000 : ℝ)^8273 ≤ (1847482059189/12500000000000 : ℝ)^6225 := by
    have hnat : (118628831 : ℕ)^8273*12500000000000^6225 ≤ 1847482059189^6225*500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118628831 500000000 1847482059189 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643558201/1250000000 : ℝ)^8273 ≤ (41382905126093/100000000000000 : ℝ)^6225 := by
    have hnat : (643558201 : ℕ)^8273*100000000000000^6225 ≤ 41382905126093^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643558201 1250000000 41382905126093 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344143793/2500000000 : ℝ), (-118628831/500000000 : ℝ), (643558201/1250000000 : ℝ)] ![(43837238390739/100000000000000 : ℝ), (1847482059189/12500000000000 : ℝ), (41382905126093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344143793/2500000000 : ℝ)|^8273 ≤ (43837238390739/100000000000000 : ℝ)^6225
        have hw : |(1344143793/2500000000 : ℝ)|=(1344143793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118628831/500000000 : ℝ)|^8273 ≤ (1847482059189/12500000000000 : ℝ)^6225
        have hw : |(-118628831/500000000 : ℝ)|=(118628831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643558201/1250000000 : ℝ)|^8273 ≤ (41382905126093/100000000000000 : ℝ)^6225
        have hw : |(643558201/1250000000 : ℝ)|=(643558201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s2_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688287667/5000000000 : ℝ)*x 0 + (643558179/1250000000 : ℝ)*x 1 + (-1186288317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688287667/5000000000 : ℝ)^8273 ≤ (43837240146139/100000000000000 : ℝ)^6225 := by
    have hnat : (2688287667 : ℕ)^8273*100000000000000^6225 ≤ 43837240146139^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688287667 5000000000 43837240146139 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643558179/1250000000 : ℝ)^8273 ≤ (20691451623/50000000000 : ℝ)^6225 := by
    have hnat : (643558179 : ℕ)^8273*50000000000^6225 ≤ 20691451623^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643558179 1250000000 20691451623 50000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1186288317/5000000000 : ℝ)^8273 ≤ (14779856589417/100000000000000 : ℝ)^6225 := by
    have hnat : (1186288317 : ℕ)^8273*100000000000000^6225 ≤ 14779856589417^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186288317 5000000000 14779856589417 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688287667/5000000000 : ℝ), (643558179/1250000000 : ℝ), (-1186288317/5000000000 : ℝ)] ![(43837240146139/100000000000000 : ℝ), (20691451623/50000000000 : ℝ), (14779856589417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688287667/5000000000 : ℝ)|^8273 ≤ (43837240146139/100000000000000 : ℝ)^6225
        have hw : |(2688287667/5000000000 : ℝ)|=(2688287667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643558179/1250000000 : ℝ)|^8273 ≤ (20691451623/50000000000 : ℝ)^6225
        have hw : |(643558179/1250000000 : ℝ)|=(643558179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1186288317/5000000000 : ℝ)|^8273 ≤ (14779856589417/100000000000000 : ℝ)^6225
        have hw : |(-1186288317/5000000000 : ℝ)|=(1186288317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s2_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545165707/1250000000 : ℝ)*x 0 + (4008877641/10000000000 : ℝ)*x 1 + (4744995801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545165707/1250000000 : ℝ)^8273 ≤ (33193607580261/100000000000000 : ℝ)^6225 := by
    have hnat : (545165707 : ℕ)^8273*100000000000000^6225 ≤ 33193607580261^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545165707 1250000000 33193607580261 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4008877641/10000000000 : ℝ)^8273 ≤ (29676924832951/100000000000000 : ℝ)^6225 := by
    have hnat : (4008877641 : ℕ)^8273*100000000000000^6225 ≤ 29676924832951^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008877641 10000000000 29676924832951 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4744995801/10000000000 : ℝ)^8273 ≤ (37129467570749/100000000000000 : ℝ)^6225 := by
    have hnat : (4744995801 : ℕ)^8273*100000000000000^6225 ≤ 37129467570749^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4744995801 10000000000 37129467570749 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545165707/1250000000 : ℝ), (4008877641/10000000000 : ℝ), (4744995801/10000000000 : ℝ)] ![(33193607580261/100000000000000 : ℝ), (29676924832951/100000000000000 : ℝ), (37129467570749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545165707/1250000000 : ℝ)|^8273 ≤ (33193607580261/100000000000000 : ℝ)^6225
        have hw : |(545165707/1250000000 : ℝ)|=(545165707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4008877641/10000000000 : ℝ)|^8273 ≤ (29676924832951/100000000000000 : ℝ)^6225
        have hw : |(4008877641/10000000000 : ℝ)|=(4008877641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4744995801/10000000000 : ℝ)|^8273 ≤ (37129467570749/100000000000000 : ℝ)^6225
        have hw : |(4744995801/10000000000 : ℝ)|=(4744995801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s2_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-435495383/2000000000 : ℝ)*x 0 + (257558141/500000000 : ℝ)*x 1 + (5520295677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435495383/2000000000 : ℝ)^8273 ≤ (2637381375419/20000000000000 : ℝ)^6225 := by
    have hnat : (435495383 : ℕ)^8273*20000000000000^6225 ≤ 2637381375419^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435495383 2000000000 2637381375419 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257558141/500000000 : ℝ)^8273 ≤ (41411720173067/100000000000000 : ℝ)^6225 := by
    have hnat : (257558141 : ℕ)^8273*100000000000000^6225 ≤ 41411720173067^6225*500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257558141 500000000 41411720173067 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520295677/10000000000 : ℝ)^8273 ≤ (22700686467011/50000000000000 : ℝ)^6225 := by
    have hnat : (5520295677 : ℕ)^8273*50000000000000^6225 ≤ 22700686467011^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520295677 10000000000 22700686467011 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435495383/2000000000 : ℝ), (257558141/500000000 : ℝ), (5520295677/10000000000 : ℝ)] ![(2637381375419/20000000000000 : ℝ), (41411720173067/100000000000000 : ℝ), (22700686467011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435495383/2000000000 : ℝ)|^8273 ≤ (2637381375419/20000000000000 : ℝ)^6225
        have hw : |(-435495383/2000000000 : ℝ)|=(435495383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257558141/500000000 : ℝ)|^8273 ≤ (41411720173067/100000000000000 : ℝ)^6225
        have hw : |(257558141/500000000 : ℝ)|=(257558141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520295677/10000000000 : ℝ)|^8273 ≤ (22700686467011/50000000000000 : ℝ)^6225
        have hw : |(5520295677/10000000000 : ℝ)|=(5520295677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s2_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132048521/250000000 : ℝ)*x 0 + (-2000746473/10000000000 : ℝ)*x 1 + (1380073943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132048521/250000000 : ℝ)^8273 ≤ (10703695033113/25000000000000 : ℝ)^6225 := by
    have hnat : (132048521 : ℕ)^8273*25000000000000^6225 ≤ 10703695033113^6225*250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132048521 250000000 10703695033113 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000746473/10000000000 : ℝ)^8273 ≤ (73649036817/625000000000 : ℝ)^6225 := by
    have hnat : (2000746473 : ℕ)^8273*625000000000^6225 ≤ 73649036817^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000746473 10000000000 73649036817 625000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380073943/2500000000 : ℝ)^8273 ≤ (11350343493099/25000000000000 : ℝ)^6225 := by
    have hnat : (1380073943 : ℕ)^8273*25000000000000^6225 ≤ 11350343493099^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380073943 2500000000 11350343493099 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132048521/250000000 : ℝ), (-2000746473/10000000000 : ℝ), (1380073943/2500000000 : ℝ)] ![(10703695033113/25000000000000 : ℝ), (73649036817/625000000000 : ℝ), (11350343493099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132048521/250000000 : ℝ)|^8273 ≤ (10703695033113/25000000000000 : ℝ)^6225
        have hw : |(132048521/250000000 : ℝ)|=(132048521/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000746473/10000000000 : ℝ)|^8273 ≤ (73649036817/625000000000 : ℝ)^6225
        have hw : |(-2000746473/10000000000 : ℝ)|=(2000746473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380073943/2500000000 : ℝ)|^8273 ≤ (11350343493099/25000000000000 : ℝ)^6225
        have hw : |(1380073943/2500000000 : ℝ)|=(1380073943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s2_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2640970539/5000000000 : ℝ)*x 0 + (86254619/156250000 : ℝ)*x 1 + (-1000373181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640970539/5000000000 : ℝ)^8273 ≤ (856295653927/2000000000000 : ℝ)^6225 := by
    have hnat : (2640970539 : ℕ)^8273*2000000000000^6225 ≤ 856295653927^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640970539 5000000000 856295653927 2000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86254619/156250000 : ℝ)^8273 ≤ (45401372267277/100000000000000 : ℝ)^6225 := by
    have hnat : (86254619 : ℕ)^8273*100000000000000^6225 ≤ 45401372267277^6225*156250000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86254619 156250000 45401372267277 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000373181/5000000000 : ℝ)^8273 ≤ (2945961255469/25000000000000 : ℝ)^6225 := by
    have hnat : (1000373181 : ℕ)^8273*25000000000000^6225 ≤ 2945961255469^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000373181 5000000000 2945961255469 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640970539/5000000000 : ℝ), (86254619/156250000 : ℝ), (-1000373181/5000000000 : ℝ)] ![(856295653927/2000000000000 : ℝ), (45401372267277/100000000000000 : ℝ), (2945961255469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640970539/5000000000 : ℝ)|^8273 ≤ (856295653927/2000000000000 : ℝ)^6225
        have hw : |(2640970539/5000000000 : ℝ)|=(2640970539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86254619/156250000 : ℝ)|^8273 ≤ (45401372267277/100000000000000 : ℝ)^6225
        have hw : |(86254619/156250000 : ℝ)|=(86254619/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000373181/5000000000 : ℝ)|^8273 ≤ (2945961255469/25000000000000 : ℝ)^6225
        have hw : |(-1000373181/5000000000 : ℝ)|=(1000373181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s2_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361564139/10000000000 : ℝ)*x 0 + (947938899/2000000000 : ℝ)*x 1 + (2007116939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361564139/10000000000 : ℝ)^8273 ≤ (265568158581/800000000000 : ℝ)^6225 := by
    have hnat : (4361564139 : ℕ)^8273*800000000000^6225 ≤ 265568158581^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361564139 10000000000 265568158581 800000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947938899/2000000000 : ℝ)^8273 ≤ (1853717376137/5000000000000 : ℝ)^6225 := by
    have hnat : (947938899 : ℕ)^8273*5000000000000^6225 ≤ 1853717376137^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947938899 2000000000 1853717376137 5000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007116939/5000000000 : ℝ)^8273 ≤ (14864816320877/50000000000000 : ℝ)^6225 := by
    have hnat : (2007116939 : ℕ)^8273*50000000000000^6225 ≤ 14864816320877^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007116939 5000000000 14864816320877 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361564139/10000000000 : ℝ), (947938899/2000000000 : ℝ), (2007116939/5000000000 : ℝ)] ![(265568158581/800000000000 : ℝ), (1853717376137/5000000000000 : ℝ), (14864816320877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361564139/10000000000 : ℝ)|^8273 ≤ (265568158581/800000000000 : ℝ)^6225
        have hw : |(4361564139/10000000000 : ℝ)|=(4361564139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(947938899/2000000000 : ℝ)|^8273 ≤ (1853717376137/5000000000000 : ℝ)^6225
        have hw : |(947938899/2000000000 : ℝ)|=(947938899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2007116939/5000000000 : ℝ)|^8273 ≤ (14864816320877/50000000000000 : ℝ)^6225
        have hw : |(2007116939/5000000000 : ℝ)|=(2007116939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5181/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1059/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (439/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3339/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5181/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1059/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5181/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1059/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5181/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1059/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5181/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1059/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5181/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1059/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5181/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1059/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1059/20000 : ℝ) ^ (517/128 : ℝ) ≤ (28033341225099/4000000000000000000 : ℝ) := by
    have hpowers : (1059/20000 : ℝ)^517 ≤ (28033341225099/4000000000000000000 : ℝ)^128 := by
      have hnat : (1059 : ℕ)^517*4000000000000000000^128 ≤ 28033341225099^128*20000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1059 20000 28033341225099 4000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1059/20000 : ℝ)) (X := (28033341225099/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (5181/25000 : ℝ) ^ (517/128 : ℝ) ≤ (34691579968069333/20000000000000000000 : ℝ) := by
    have hpowers : (5181/25000 : ℝ)^517 ≤ (34691579968069333/20000000000000000000 : ℝ)^128 := by
      have hnat : (5181 : ℕ)^517*20000000000000000000^128 ≤ 34691579968069333^128*25000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5181 25000 34691579968069333 20000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5181/25000 : ℝ)) (X := (34691579968069333/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000028033341225099/2000000000000000000 : ℝ) ≤ (5000017351299591/5000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (2000028033341225099/2000000000000000000 : ℝ)^128 ≤ (5000017351299591/5000000000000000 : ℝ)^517 := by
      have hnat : (2000028033341225099 : ℕ)^128*5000000000000000^517 ≤ 5000017351299591^517*2000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000028033341225099 2000000000000000000 5000017351299591 5000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000017351299591/5000000000000000 : ℝ)) (X := (2000028033341225099/2000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (5008707936668548707/5000000000000000000 : ℝ) ≤ (2501077259515067/2500000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (5008707936668548707/5000000000000000000 : ℝ)^128 ≤ (2501077259515067/2500000000000000 : ℝ)^517 := by
      have hnat : (5008707936668548707 : ℕ)^128*2500000000000000^517 ≤ 2501077259515067^517*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5008707936668548707 5000000000000000000 2501077259515067 2500000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501077259515067/2500000000000000 : ℝ)) (X := (5008707936668548707/5000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10034691579968069333/10000000000000000000 : ℝ) ≤ (5004291686760677/5000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (10034691579968069333/10000000000000000000 : ℝ)^128 ≤ (5004291686760677/5000000000000000 : ℝ)^517 := by
      have hnat : (10034691579968069333 : ℕ)^128*5000000000000000^517 ≤ 5004291686760677^517*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10034691579968069333 10000000000000000000 5004291686760677 5000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004291686760677/5000000000000000 : ℝ)) (X := (10034691579968069333/10000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28033341225099/4000000000000000000 : ℝ) ≤ ((25707545035644979723/25715000000000000000 : ℝ)+2*(2137167730543/771450000000000 : ℝ)*(1059/20000 : ℝ))^(517/128 : ℝ) := by
    rw [show (25707545035644979723/25715000000000000000 : ℝ)+2*(2137167730543/771450000000000 : ℝ)*(1059/20000 : ℝ)=(5000017351299591/5000000000000000 : ℝ) by norm_num, show 1+2*(28033341225099/4000000000000000000 : ℝ)=(2000028033341225099/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34691579968069333/20000000000000000000 : ℝ)+(28033341225099/4000000000000000000 : ℝ) ≤ ((25707545035644979723/25715000000000000000 : ℝ)+(2137167730543/771450000000000 : ℝ)*((5181/25000 : ℝ)+(1059/20000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (25707545035644979723/25715000000000000000 : ℝ)+(2137167730543/771450000000000 : ℝ)*((5181/25000 : ℝ)+(1059/20000 : ℝ))=(2501077259515067/2500000000000000 : ℝ) by norm_num, show 1+(34691579968069333/20000000000000000000 : ℝ)+(28033341225099/4000000000000000000 : ℝ)=(5008707936668548707/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34691579968069333/20000000000000000000 : ℝ) ≤ ((25707545035644979723/25715000000000000000 : ℝ)+2*(2137167730543/771450000000000 : ℝ)*(5181/25000 : ℝ))^(517/128 : ℝ) := by
    rw [show (25707545035644979723/25715000000000000000 : ℝ)+2*(2137167730543/771450000000000 : ℝ)*(5181/25000 : ℝ)=(5004291686760677/5000000000000000 : ℝ) by norm_num, show 1+2*(34691579968069333/20000000000000000000 : ℝ)=(10034691579968069333/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25707545035644979723/25715000000000000000 : ℝ)*(X 1 0+X 2 0)+(2137167730543/771450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (1059/20000 : ℝ)) (hi := (5181/25000 : ℝ)) (c := (25707545035644979723/25715000000000000000 : ℝ)) (alpha := (2137167730543/771450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25707545035644979723/25715000000000000000 : ℝ)*(X 0 1+X 2 1)+(2137167730543/771450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (1059/20000 : ℝ)) (hi := (5181/25000 : ℝ)) (c := (25707545035644979723/25715000000000000000 : ℝ)) (alpha := (2137167730543/771450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25707545035644979723/25715000000000000000 : ℝ)*(X 0 2+X 1 2)+(2137167730543/771450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (1059/20000 : ℝ)) (hi := (5181/25000 : ℝ)) (c := (25707545035644979723/25715000000000000000 : ℝ)) (alpha := (2137167730543/771450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2177355643/10000000000 : ℝ)*X 0 0+(5523021499/10000000000 : ℝ)*X 0 1+(1287116279/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1344143793/2500000000 : ℝ)*X 1 0+(-118628831/500000000 : ℝ)*X 1 1+(643558201/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688287667/5000000000 : ℝ)*X 2 0+(643558179/1250000000 : ℝ)*X 2 1+(-1186288317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545165707/1250000000 : ℝ)*X 0 0+(4008877641/10000000000 : ℝ)*X 0 1+(4744995801/10000000000 : ℝ)*X 0 2+(545165707/1250000000 : ℝ)*X 1 0+(4008877641/10000000000 : ℝ)*X 1 1+(4744995801/10000000000 : ℝ)*X 1 2+(545165707/1250000000 : ℝ)*X 2 0+(4008877641/10000000000 : ℝ)*X 2 1+(4744995801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-435495383/2000000000 : ℝ)*X 0 0+(257558141/500000000 : ℝ)*X 0 1+(5520295677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132048521/250000000 : ℝ)*X 1 0+(-2000746473/10000000000 : ℝ)*X 1 1+(1380073943/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640970539/5000000000 : ℝ)*X 2 0+(86254619/156250000 : ℝ)*X 2 1+(-1000373181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361564139/10000000000 : ℝ)*X 0 0+(947938899/2000000000 : ℝ)*X 0 1+(2007116939/5000000000 : ℝ)*X 0 2+(4361564139/10000000000 : ℝ)*X 1 0+(947938899/2000000000 : ℝ)*X 1 1+(2007116939/5000000000 : ℝ)*X 1 2+(4361564139/10000000000 : ℝ)*X 2 0+(947938899/2000000000 : ℝ)*X 2 1+(2007116939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4330035076973147676896971167/642875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6697703/25000000000000 : ℝ)*(base1) + (1211379371/100000000000000 : ℝ)*(base19) + (645911981/50000000000000 : ℝ)*(base23) + (975609/781250000000 : ℝ)*(upper3) + (67097911/50000000000000 : ℝ)*(upper5) + (2014173580780143/100000000000000 : ℝ)*(major0) + (2014173580780143/100000000000000 : ℝ)*(major1) + (2014173580780143/100000000000000 : ℝ)*(major2) + (667459983591231/25000000000000 : ℝ)*(sp0) + (533970861040719/20000000000000 : ℝ)*(sp1) + (533970844951801/20000000000000 : ℝ)*(sp2) + (1358484383861899/100000000000000 : ℝ)*(sp3) + (3121801771/20000000000000 : ℝ)*(sp4) + (14019621/200000000000 : ℝ)*(sp7) + (339622855115803/25000000000000 : ℝ)*(f.failure) + (1334927758291483/50000000000000 : ℝ)*(f.sum) + (54503351369061/25715000000000000000000000000 : ℝ)*base65 + (13330109954508159611/2571500000000000000000000000000000 : ℝ)*base68 + (15551490414092659611/2571500000000000000000000000000000 : ℝ)*base70 + (4061944752911659611/2571500000000000000000000000000000 : ℝ)*base72 + (109292380237419/25715000000000000000000000000 : ℝ)*base74 + (12847513376925840389/2571500000000000000000000000000000 : ℝ)*base75 + (1735352690006659611/2571500000000000000000000000000000 : ℝ)*base78 + (15086297837864159611/2571500000000000000000000000000000 : ℝ)*base80 + (75754030442469/25715000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (10147993/1250000000000000000000 : ℝ)*base89 + (10147993/1250000000000000000000 : ℝ)*base91 + (10147993/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3753783278296935836794585851/642875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1136118419/100000000000000 : ℝ)*(base19) + (1357150611/100000000000000 : ℝ)*(base23) + (165293199/100000000000000 : ℝ)*(upper3) + (30703887/100000000000000 : ℝ)*(lower4) + (2868699/2500000000000 : ℝ)*(upper5) + (2043743215946421/100000000000000 : ℝ)*(major0) + (2043743215946421/100000000000000 : ℝ)*(major1) + (2043743215946421/100000000000000 : ℝ)*(major2) + (1241797571/12500000000000 : ℝ)*(sp1) + (12213544743/100000000000000 : ℝ)*(sp2) + (169315694115853/6250000000000 : ℝ)*(sp4) + (135452001767733/5000000000000 : ℝ)*(sp5) + (1354518767579147/50000000000000 : ℝ)*(sp6) + (689217565701991/50000000000000 : ℝ)*(sp7) + (689217565701991/50000000000000 : ℝ)*(f.failure) + (169315694115853/6250000000000 : ℝ)*(f.sum) + (6352834121533/6428750000000000000000000000 : ℝ)*base65 + (9889000281844521383/2571500000000000000000000000000000 : ℝ)*base67 + (13568828157258478617/2571500000000000000000000000000000 : ℝ)*base70 + (12919443231048521383/2571500000000000000000000000000000 : ℝ)*base71 + (7314593115231/3214375000000000000000000000 : ℝ)*base74 + (15229597916229521383/2571500000000000000000000000000000 : ℝ)*base75 + (1132206679191521383/2571500000000000000000000000000000 : ℝ)*base77 + (5218910137864521383/2571500000000000000000000000000000 : ℝ)*base79 + (33210176357597/6428750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (32579/2500000000000000000000 : ℝ)*base90 + (32579/2500000000000000000000 : ℝ)*base92 + (32579/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1080_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5181/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1059/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3339/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1080_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3339/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1080_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1080_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1080_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (439/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3339/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1080_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
