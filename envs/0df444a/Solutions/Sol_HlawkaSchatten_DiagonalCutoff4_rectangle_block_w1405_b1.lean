-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1405_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:21.963377+00:00
-- url     : https://prove2.me/submissions/acdd4d5e-6734-43b4-8a91-99c7c4f0a8d9

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
theorem support_rectangle_w1405_s3_0 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-497388107/2500000000 : ℝ)*x 0 + (5419780001/10000000000 : ℝ)*x 1 + (5236823159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497388107/2500000000 : ℝ)^4365 ≤ (1516133314133/12500000000000 : ℝ)^3341 := by
    have hnat : (497388107 : ℕ)^4365*12500000000000^3341 ≤ 1516133314133^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497388107 2500000000 1516133314133 12500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419780001/10000000000 : ℝ)^4365 ≤ (22460444889239/50000000000000 : ℝ)^3341 := by
    have hnat : (5419780001 : ℕ)^4365*50000000000000^3341 ≤ 22460444889239^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419780001 10000000000 22460444889239 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236823159/10000000000 : ℝ)^4365 ≤ (21475021845931/50000000000000 : ℝ)^3341 := by
    have hnat : (5236823159 : ℕ)^4365*50000000000000^3341 ≤ 21475021845931^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236823159 10000000000 21475021845931 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-497388107/2500000000 : ℝ), (5419780001/10000000000 : ℝ), (5236823159/10000000000 : ℝ)] ![(1516133314133/12500000000000 : ℝ), (22460444889239/50000000000000 : ℝ), (21475021845931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-497388107/2500000000 : ℝ)|^4365 ≤ (1516133314133/12500000000000 : ℝ)^3341
        have hw : |(-497388107/2500000000 : ℝ)|=(497388107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419780001/10000000000 : ℝ)|^4365 ≤ (22460444889239/50000000000000 : ℝ)^3341
        have hw : |(5419780001/10000000000 : ℝ)|=(5419780001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236823159/10000000000 : ℝ)|^4365 ≤ (21475021845931/50000000000000 : ℝ)^3341
        have hw : |(5236823159/10000000000 : ℝ)|=(5236823159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_1 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350478001/10000000000 : ℝ)*x 0 + (-260365299/1250000000 : ℝ)*x 1 + (2618411551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350478001/10000000000 : ℝ)^4365 ≤ (11042979333763/25000000000000 : ℝ)^3341 := by
    have hnat : (5350478001 : ℕ)^4365*25000000000000^3341 ≤ 11042979333763^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350478001 10000000000 11042979333763 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260365299/1250000000 : ℝ)^4365 ≤ (12878039573819/100000000000000 : ℝ)^3341 := by
    have hnat : (260365299 : ℕ)^4365*100000000000000^3341 ≤ 12878039573819^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260365299 1250000000 12878039573819 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618411551/5000000000 : ℝ)^4365 ≤ (42950043081091/100000000000000 : ℝ)^3341 := by
    have hnat : (2618411551 : ℕ)^4365*100000000000000^3341 ≤ 42950043081091^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618411551 5000000000 42950043081091 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350478001/10000000000 : ℝ), (-260365299/1250000000 : ℝ), (2618411551/5000000000 : ℝ)] ![(11042979333763/25000000000000 : ℝ), (12878039573819/100000000000000 : ℝ), (42950043081091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350478001/10000000000 : ℝ)|^4365 ≤ (11042979333763/25000000000000 : ℝ)^3341
        have hw : |(5350478001/10000000000 : ℝ)|=(5350478001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260365299/1250000000 : ℝ)|^4365 ≤ (12878039573819/100000000000000 : ℝ)^3341
        have hw : |(-260365299/1250000000 : ℝ)|=(260365299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618411551/5000000000 : ℝ)|^4365 ≤ (42950043081091/100000000000000 : ℝ)^3341
        have hw : |(2618411551/5000000000 : ℝ)|=(2618411551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_2 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350477993/10000000000 : ℝ)*x 0 + (1047364633/2000000000 : ℝ)*x 1 + (-2082922319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350477993/10000000000 : ℝ)^4365 ≤ (11042979312191/25000000000000 : ℝ)^3341 := by
    have hnat : (5350477993 : ℕ)^4365*25000000000000^3341 ≤ 11042979312191^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350477993 10000000000 11042979312191 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047364633/2000000000 : ℝ)^4365 ≤ (21475021878077/50000000000000 : ℝ)^3341 := by
    have hnat : (1047364633 : ℕ)^4365*50000000000000^3341 ≤ 21475021878077^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047364633 2000000000 21475021878077 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082922319/10000000000 : ℝ)^4365 ≤ (12878038984151/100000000000000 : ℝ)^3341 := by
    have hnat : (2082922319 : ℕ)^4365*100000000000000^3341 ≤ 12878038984151^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082922319 10000000000 12878038984151 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350477993/10000000000 : ℝ), (1047364633/2000000000 : ℝ), (-2082922319/10000000000 : ℝ)] ![(11042979312191/25000000000000 : ℝ), (21475021878077/50000000000000 : ℝ), (12878038984151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350477993/10000000000 : ℝ)|^4365 ≤ (11042979312191/25000000000000 : ℝ)^3341
        have hw : |(5350477993/10000000000 : ℝ)|=(5350477993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047364633/2000000000 : ℝ)|^4365 ≤ (21475021878077/50000000000000 : ℝ)^3341
        have hw : |(1047364633/2000000000 : ℝ)|=(1047364633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082922319/10000000000 : ℝ)|^4365 ≤ (12878038984151/100000000000000 : ℝ)^3341
        have hw : |(-2082922319/10000000000 : ℝ)|=(2082922319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_3 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309669991/10000000000 : ℝ)*x 0 + (4117566407/10000000000 : ℝ)*x 1 + (1127471381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309669991/10000000000 : ℝ)^4365 ≤ (2081051985773/6250000000000 : ℝ)^3341 := by
    have hnat : (4309669991 : ℕ)^4365*6250000000000^3341 ≤ 2081051985773^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309669991 10000000000 2081051985773 6250000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4117566407/10000000000 : ℝ)^4365 ≤ (31371108358931/100000000000000 : ℝ)^3341 := by
    have hnat : (4117566407 : ℕ)^4365*100000000000000^3341 ≤ 31371108358931^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117566407 10000000000 31371108358931 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127471381/2500000000 : ℝ)^4365 ≤ (17666029925451/50000000000000 : ℝ)^3341 := by
    have hnat : (1127471381 : ℕ)^4365*50000000000000^3341 ≤ 17666029925451^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127471381 2500000000 17666029925451 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309669991/10000000000 : ℝ), (4117566407/10000000000 : ℝ), (1127471381/2500000000 : ℝ)] ![(2081051985773/6250000000000 : ℝ), (31371108358931/100000000000000 : ℝ), (17666029925451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309669991/10000000000 : ℝ)|^4365 ≤ (2081051985773/6250000000000 : ℝ)^3341
        have hw : |(4309669991/10000000000 : ℝ)|=(4309669991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4117566407/10000000000 : ℝ)|^4365 ≤ (31371108358931/100000000000000 : ℝ)^3341
        have hw : |(4117566407/10000000000 : ℝ)|=(4117566407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127471381/2500000000 : ℝ)|^4365 ≤ (17666029925451/50000000000000 : ℝ)^3341
        have hw : |(1127471381/2500000000 : ℝ)|=(1127471381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_4 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-497392261/2500000000 : ℝ)*x 0 + (2618780601/5000000000 : ℝ)*x 1 + (677379679/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497392261/2500000000 : ℝ)^4365 ≤ (151614985723/1250000000000 : ℝ)^3341 := by
    have hnat : (497392261 : ℕ)^4365*1250000000000^3341 ≤ 151614985723^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497392261 2500000000 151614985723 1250000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618780601/5000000000 : ℝ)^4365 ≤ (42957952199141/100000000000000 : ℝ)^3341 := by
    have hnat : (2618780601 : ℕ)^4365*100000000000000^3341 ≤ 42957952199141^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618780601 5000000000 42957952199141 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677379679/1250000000 : ℝ)^4365 ≤ (44912848924783/100000000000000 : ℝ)^3341 := by
    have hnat : (677379679 : ℕ)^4365*100000000000000^3341 ≤ 44912848924783^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677379679 1250000000 44912848924783 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-497392261/2500000000 : ℝ), (2618780601/5000000000 : ℝ), (677379679/1250000000 : ℝ)] ![(151614985723/1250000000000 : ℝ), (42957952199141/100000000000000 : ℝ), (44912848924783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-497392261/2500000000 : ℝ)|^4365 ≤ (151614985723/1250000000000 : ℝ)^3341
        have hw : |(-497392261/2500000000 : ℝ)|=(497392261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618780601/5000000000 : ℝ)|^4365 ≤ (42957952199141/100000000000000 : ℝ)^3341
        have hw : |(2618780601/5000000000 : ℝ)|=(2618780601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677379679/1250000000 : ℝ)|^4365 ≤ (44912848924783/100000000000000 : ℝ)^3341
        have hw : |(677379679/1250000000 : ℝ)|=(677379679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_5 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303028867/10000000000 : ℝ)*x 0 + (-1900707511/10000000000 : ℝ)*x 1 + (677379727/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303028867/10000000000 : ℝ)^4365 ≤ (43660826734653/100000000000000 : ℝ)^3341 := by
    have hnat : (5303028867 : ℕ)^4365*100000000000000^3341 ≤ 43660826734653^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303028867 10000000000 43660826734653 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1900707511/10000000000 : ℝ)^4365 ≤ (5713160081859/50000000000000 : ℝ)^3341 := by
    have hnat : (1900707511 : ℕ)^4365*50000000000000^3341 ≤ 5713160081859^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900707511 10000000000 5713160081859 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677379727/1250000000 : ℝ)^4365 ≤ (11228213270703/25000000000000 : ℝ)^3341 := by
    have hnat : (677379727 : ℕ)^4365*25000000000000^3341 ≤ 11228213270703^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677379727 1250000000 11228213270703 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303028867/10000000000 : ℝ), (-1900707511/10000000000 : ℝ), (677379727/1250000000 : ℝ)] ![(43660826734653/100000000000000 : ℝ), (5713160081859/50000000000000 : ℝ), (11228213270703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303028867/10000000000 : ℝ)|^4365 ≤ (43660826734653/100000000000000 : ℝ)^3341
        have hw : |(5303028867/10000000000 : ℝ)|=(5303028867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1900707511/10000000000 : ℝ)|^4365 ≤ (5713160081859/50000000000000 : ℝ)^3341
        have hw : |(-1900707511/10000000000 : ℝ)|=(1900707511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677379727/1250000000 : ℝ)|^4365 ≤ (11228213270703/25000000000000 : ℝ)^3341
        have hw : |(677379727/1250000000 : ℝ)|=(677379727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_6 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331439359/625000000 : ℝ)*x 0 + (5419037137/10000000000 : ℝ)*x 1 + (-950353623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331439359/625000000 : ℝ)^4365 ≤ (43660836168207/100000000000000 : ℝ)^3341 := by
    have hnat : (331439359 : ℕ)^4365*100000000000000^3341 ≤ 43660836168207^3341*625000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331439359 625000000 43660836168207 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419037137/10000000000 : ℝ)^4365 ≤ (8982569146093/20000000000000 : ℝ)^3341 := by
    have hnat : (5419037137 : ℕ)^4365*20000000000000^3341 ≤ 8982569146093^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419037137 10000000000 8982569146093 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (950353623/5000000000 : ℝ)^4365 ≤ (11426318082369/100000000000000 : ℝ)^3341 := by
    have hnat : (950353623 : ℕ)^4365*100000000000000^3341 ≤ 11426318082369^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950353623 5000000000 11426318082369 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331439359/625000000 : ℝ), (5419037137/10000000000 : ℝ), (-950353623/5000000000 : ℝ)] ![(43660836168207/100000000000000 : ℝ), (8982569146093/20000000000000 : ℝ), (11426318082369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331439359/625000000 : ℝ)|^4365 ≤ (43660836168207/100000000000000 : ℝ)^3341
        have hw : |(331439359/625000000 : ℝ)|=(331439359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419037137/10000000000 : ℝ)|^4365 ≤ (8982569146093/20000000000000 : ℝ)^3341
        have hw : |(5419037137/10000000000 : ℝ)|=(5419037137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-950353623/5000000000 : ℝ)|^4365 ≤ (11426318082369/100000000000000 : ℝ)^3341
        have hw : |(-950353623/5000000000 : ℝ)|=(950353623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_7 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309705899/10000000000 : ℝ)*x 0 + (225415131/500000000 : ℝ)*x 1 + (4119157491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309705899/10000000000 : ℝ)^4365 ≤ (16648597115497/50000000000000 : ℝ)^3341 := by
    have hnat : (4309705899 : ℕ)^4365*50000000000000^3341 ≤ 16648597115497^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309705899 10000000000 16648597115497 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225415131/500000000 : ℝ)^4365 ≤ (35315858828369/100000000000000 : ℝ)^3341 := by
    have hnat : (225415131 : ℕ)^4365*100000000000000^3341 ≤ 35315858828369^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225415131 500000000 35315858828369 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4119157491/10000000000 : ℝ)^4365 ≤ (1255477876979/4000000000000 : ℝ)^3341 := by
    have hnat : (4119157491 : ℕ)^4365*4000000000000^3341 ≤ 1255477876979^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119157491 10000000000 1255477876979 4000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309705899/10000000000 : ℝ), (225415131/500000000 : ℝ), (4119157491/10000000000 : ℝ)] ![(16648597115497/50000000000000 : ℝ), (35315858828369/100000000000000 : ℝ), (1255477876979/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309705899/10000000000 : ℝ)|^4365 ≤ (16648597115497/50000000000000 : ℝ)^3341
        have hw : |(4309705899/10000000000 : ℝ)|=(4309705899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225415131/500000000 : ℝ)|^4365 ≤ (35315858828369/100000000000000 : ℝ)^3341
        have hw : |(225415131/500000000 : ℝ)|=(225415131/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4119157491/10000000000 : ℝ)|^4365 ≤ (1255477876979/4000000000000 : ℝ)^3341
        have hw : |(4119157491/10000000000 : ℝ)|=(4119157491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_8 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8201459/1000000000 : ℝ)*x 0 + (2855772547/5000000000 : ℝ)*x 1 + (1207177029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8201459/1000000000 : ℝ)^4365 ≤ (188152090679/100000000000000 : ℝ)^3341 := by
    have hnat : (8201459 : ℕ)^4365*100000000000000^3341 ≤ 188152090679^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8201459 1000000000 188152090679 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2855772547/5000000000 : ℝ)^4365 ≤ (24053030230361/50000000000000 : ℝ)^3341 := by
    have hnat : (2855772547 : ℕ)^4365*50000000000000^3341 ≤ 24053030230361^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855772547 5000000000 24053030230361 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207177029/2000000000 : ℝ)^4365 ≤ (25852893714159/50000000000000 : ℝ)^3341 := by
    have hnat : (1207177029 : ℕ)^4365*50000000000000^3341 ≤ 25852893714159^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207177029 2000000000 25852893714159 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8201459/1000000000 : ℝ), (2855772547/5000000000 : ℝ), (1207177029/2000000000 : ℝ)] ![(188152090679/100000000000000 : ℝ), (24053030230361/50000000000000 : ℝ), (25852893714159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8201459/1000000000 : ℝ)|^4365 ≤ (188152090679/100000000000000 : ℝ)^3341
        have hw : |(-8201459/1000000000 : ℝ)|=(8201459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2855772547/5000000000 : ℝ)|^4365 ≤ (24053030230361/50000000000000 : ℝ)^3341
        have hw : |(2855772547/5000000000 : ℝ)|=(2855772547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207177029/2000000000 : ℝ)|^4365 ≤ (25852893714159/50000000000000 : ℝ)^3341
        have hw : |(1207177029/2000000000 : ℝ)|=(1207177029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_9 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519593921/5000000000 : ℝ)*x 0 + (-838570189/2000000000 : ℝ)*x 1 + (874301331/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519593921/5000000000 : ℝ)^4365 ≤ (5191772356847/100000000000000 : ℝ)^3341 := by
    have hnat : (519593921 : ℕ)^4365*100000000000000^3341 ≤ 5191772356847^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519593921 5000000000 5191772356847 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (838570189/2000000000 : ℝ)^4365 ≤ (32122580505753/100000000000000 : ℝ)^3341 := by
    have hnat : (838570189 : ℕ)^4365*100000000000000^3341 ≤ 32122580505753^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838570189 2000000000 32122580505753 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874301331/1250000000 : ℝ)^4365 ≤ (62685647116791/100000000000000 : ℝ)^3341 := by
    have hnat : (874301331 : ℕ)^4365*100000000000000^3341 ≤ 62685647116791^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874301331 1250000000 62685647116791 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519593921/5000000000 : ℝ), (-838570189/2000000000 : ℝ), (874301331/1250000000 : ℝ)] ![(5191772356847/100000000000000 : ℝ), (32122580505753/100000000000000 : ℝ), (62685647116791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519593921/5000000000 : ℝ)|^4365 ≤ (5191772356847/100000000000000 : ℝ)^3341
        have hw : |(519593921/5000000000 : ℝ)|=(519593921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-838570189/2000000000 : ℝ)|^4365 ≤ (32122580505753/100000000000000 : ℝ)^3341
        have hw : |(-838570189/2000000000 : ℝ)|=(838570189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(874301331/1250000000 : ℝ)|^4365 ≤ (62685647116791/100000000000000 : ℝ)^3341
        have hw : |(874301331/1250000000 : ℝ)|=(874301331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_10 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519598359/5000000000 : ℝ)*x 0 + (349721509/500000000 : ℝ)*x 1 + (-1048205577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519598359/5000000000 : ℝ)^4365 ≤ (207673211707/4000000000000 : ℝ)^3341 := by
    have hnat : (519598359 : ℕ)^4365*4000000000000^3341 ≤ 207673211707^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519598359 5000000000 207673211707 4000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349721509/500000000 : ℝ)^4365 ≤ (12537175163937/20000000000000 : ℝ)^3341 := by
    have hnat : (349721509 : ℕ)^4365*20000000000000^3341 ≤ 12537175163937^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349721509 500000000 12537175163937 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048205577/2500000000 : ℝ)^4365 ≤ (2007643366649/6250000000000 : ℝ)^3341 := by
    have hnat : (1048205577 : ℕ)^4365*6250000000000^3341 ≤ 2007643366649^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048205577 2500000000 2007643366649 6250000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519598359/5000000000 : ℝ), (349721509/500000000 : ℝ), (-1048205577/2500000000 : ℝ)] ![(207673211707/4000000000000 : ℝ), (12537175163937/20000000000000 : ℝ), (2007643366649/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519598359/5000000000 : ℝ)|^4365 ≤ (207673211707/4000000000000 : ℝ)^3341
        have hw : |(519598359/5000000000 : ℝ)|=(519598359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349721509/500000000 : ℝ)|^4365 ≤ (12537175163937/20000000000000 : ℝ)^3341
        have hw : |(349721509/500000000 : ℝ)|=(349721509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048205577/2500000000 : ℝ)|^4365 ≤ (2007643366649/6250000000000 : ℝ)^3341
        have hw : |(-1048205577/2500000000 : ℝ)|=(1048205577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s3_11 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (491723947/5000000000 : ℝ)*x 0 + (5819805437/10000000000 : ℝ)*x 1 + (2753524323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491723947/5000000000 : ℝ)^4365 ≤ (4830973100553/100000000000000 : ℝ)^3341 := by
    have hnat : (491723947 : ℕ)^4365*100000000000000^3341 ≤ 4830973100553^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491723947 5000000000 4830973100553 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5819805437/10000000000 : ℝ)^4365 ≤ (78881299099/160000000000 : ℝ)^3341 := by
    have hnat : (5819805437 : ℕ)^4365*160000000000^3341 ≤ 78881299099^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5819805437 10000000000 78881299099 160000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2753524323/5000000000 : ℝ)^4365 ≤ (9173642990531/20000000000000 : ℝ)^3341 := by
    have hnat : (2753524323 : ℕ)^4365*20000000000000^3341 ≤ 9173642990531^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753524323 5000000000 9173642990531 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(491723947/5000000000 : ℝ), (5819805437/10000000000 : ℝ), (2753524323/5000000000 : ℝ)] ![(4830973100553/100000000000000 : ℝ), (78881299099/160000000000 : ℝ), (9173642990531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(491723947/5000000000 : ℝ)|^4365 ≤ (4830973100553/100000000000000 : ℝ)^3341
        have hw : |(491723947/5000000000 : ℝ)|=(491723947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5819805437/10000000000 : ℝ)|^4365 ≤ (78881299099/160000000000 : ℝ)^3341
        have hw : |(5819805437/10000000000 : ℝ)|=(5819805437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2753524323/5000000000 : ℝ)|^4365 ≤ (9173642990531/20000000000000 : ℝ)^3341
        have hw : |(2753524323/5000000000 : ℝ)|=(2753524323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1405_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3969/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11087/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (187/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3969/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2559/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3969/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2559/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3969/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2559/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3969/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2559/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3969/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2559/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3969/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2559/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2559/25000 : ℝ) ^ (1091/256 : ℝ) ≤ (1511449533950747/25000000000000000000 : ℝ) := by
    have hpowers : (2559/25000 : ℝ)^1091 ≤ (1511449533950747/25000000000000000000 : ℝ)^256 := by
      have hnat : (2559 : ℕ)^1091*25000000000000000000^256 ≤ 1511449533950747^256*25000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2559 25000 1511449533950747 25000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2559/25000 : ℝ)) (X := (1511449533950747/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3969/25000 : ℝ) ^ (1091/256 : ℝ) ≤ (2452806765961693/6250000000000000000 : ℝ) := by
    have hpowers : (3969/25000 : ℝ)^1091 ≤ (2452806765961693/6250000000000000000 : ℝ)^256 := by
      have hnat : (3969 : ℕ)^1091*6250000000000000000^256 ≤ 2452806765961693^256*25000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3969 25000 2452806765961693 6250000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3969/25000 : ℝ)) (X := (2452806765961693/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501511449533950747/12500000000000000000 : ℝ) ≤ (10000283712687817/10000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (12501511449533950747/12500000000000000000 : ℝ)^256 ≤ (10000283712687817/10000000000000000 : ℝ)^1091 := by
      have hnat : (12501511449533950747 : ℕ)^256*10000000000000000^1091 ≤ 10000283712687817^1091*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501511449533950747 12500000000000000000 10000283712687817 10000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283712687817/10000000000000000 : ℝ)) (X := (12501511449533950747/12500000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011322676597797519/25000000000000000000 : ℝ) ≤ (1000106254920833/1000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (25011322676597797519/25000000000000000000 : ℝ)^256 ≤ (1000106254920833/1000000000000000 : ℝ)^1091 := by
      have hnat : (25011322676597797519 : ℕ)^256*1000000000000000^1091 ≤ 1000106254920833^1091*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011322676597797519 25000000000000000000 1000106254920833 1000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000106254920833/1000000000000000 : ℝ)) (X := (25011322676597797519/25000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127452806765961693/3125000000000000000 : ℝ) ≤ (10001841385728843/10000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (3127452806765961693/3125000000000000000 : ℝ)^256 ≤ (10001841385728843/10000000000000000 : ℝ)^1091 := by
      have hnat : (3127452806765961693 : ℕ)^256*10000000000000000^1091 ≤ 10001841385728843^1091*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127452806765961693 3125000000000000000 10001841385728843 10000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001841385728843/10000000000000000 : ℝ)) (X := (3127452806765961693/3125000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1511449533950747/25000000000000000000 : ℝ) ≤ ((1174701162464819703/1175000000000000000 : ℝ)+2*(778836520513/564000000000000 : ℝ)*(2559/25000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (1174701162464819703/1175000000000000000 : ℝ)+2*(778836520513/564000000000000 : ℝ)*(2559/25000 : ℝ)=(10000283712687817/10000000000000000 : ℝ) by norm_num, show 1+2*(1511449533950747/25000000000000000000 : ℝ)=(12501511449533950747/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2452806765961693/6250000000000000000 : ℝ)+(1511449533950747/25000000000000000000 : ℝ) ≤ ((1174701162464819703/1175000000000000000 : ℝ)+(778836520513/564000000000000 : ℝ)*((3969/25000 : ℝ)+(2559/25000 : ℝ)))^(1091/256 : ℝ) := by
    rw [show (1174701162464819703/1175000000000000000 : ℝ)+(778836520513/564000000000000 : ℝ)*((3969/25000 : ℝ)+(2559/25000 : ℝ))=(1000106254920833/1000000000000000 : ℝ) by norm_num, show 1+(2452806765961693/6250000000000000000 : ℝ)+(1511449533950747/25000000000000000000 : ℝ)=(25011322676597797519/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2452806765961693/6250000000000000000 : ℝ) ≤ ((1174701162464819703/1175000000000000000 : ℝ)+2*(778836520513/564000000000000 : ℝ)*(3969/25000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (1174701162464819703/1175000000000000000 : ℝ)+2*(778836520513/564000000000000 : ℝ)*(3969/25000 : ℝ)=(10001841385728843/10000000000000000 : ℝ) by norm_num, show 1+2*(2452806765961693/6250000000000000000 : ℝ)=(3127452806765961693/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1174701162464819703/1175000000000000000 : ℝ)*(X 1 0+X 2 0)+(778836520513/564000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (2559/25000 : ℝ)) (hi := (3969/25000 : ℝ)) (c := (1174701162464819703/1175000000000000000 : ℝ)) (alpha := (778836520513/564000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1174701162464819703/1175000000000000000 : ℝ)*(X 0 1+X 2 1)+(778836520513/564000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (2559/25000 : ℝ)) (hi := (3969/25000 : ℝ)) (c := (1174701162464819703/1175000000000000000 : ℝ)) (alpha := (778836520513/564000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1174701162464819703/1175000000000000000 : ℝ)*(X 0 2+X 1 2)+(778836520513/564000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (2559/25000 : ℝ)) (hi := (3969/25000 : ℝ)) (c := (1174701162464819703/1175000000000000000 : ℝ)) (alpha := (778836520513/564000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-497388107/2500000000 : ℝ)*X 0 0+(5419780001/10000000000 : ℝ)*X 0 1+(5236823159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350478001/10000000000 : ℝ)*X 1 0+(-260365299/1250000000 : ℝ)*X 1 1+(2618411551/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350477993/10000000000 : ℝ)*X 2 0+(1047364633/2000000000 : ℝ)*X 2 1+(-2082922319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4309669991/10000000000 : ℝ)*X 0 0+(4117566407/10000000000 : ℝ)*X 0 1+(1127471381/2500000000 : ℝ)*X 0 2+(4309669991/10000000000 : ℝ)*X 1 0+(4117566407/10000000000 : ℝ)*X 1 1+(1127471381/2500000000 : ℝ)*X 1 2+(4309669991/10000000000 : ℝ)*X 2 0+(4117566407/10000000000 : ℝ)*X 2 1+(1127471381/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-497392261/2500000000 : ℝ)*X 0 0+(2618780601/5000000000 : ℝ)*X 0 1+(677379679/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303028867/10000000000 : ℝ)*X 1 0+(-1900707511/10000000000 : ℝ)*X 1 1+(677379727/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331439359/625000000 : ℝ)*X 2 0+(5419037137/10000000000 : ℝ)*X 2 1+(-950353623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309705899/10000000000 : ℝ)*X 0 0+(225415131/500000000 : ℝ)*X 0 1+(4119157491/10000000000 : ℝ)*X 0 2+(4309705899/10000000000 : ℝ)*X 1 0+(225415131/500000000 : ℝ)*X 1 1+(4119157491/10000000000 : ℝ)*X 1 2+(4309705899/10000000000 : ℝ)*X 2 0+(225415131/500000000 : ℝ)*X 2 1+(4119157491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-8201459/1000000000 : ℝ)*X 0 0+(2855772547/5000000000 : ℝ)*X 0 1+(1207177029/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((519593921/5000000000 : ℝ)*X 1 0+(-838570189/2000000000 : ℝ)*X 1 1+(874301331/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((519598359/5000000000 : ℝ)*X 2 0+(349721509/500000000 : ℝ)*X 2 1+(-1048205577/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((491723947/5000000000 : ℝ)*X 0 0+(5819805437/10000000000 : ℝ)*X 0 1+(2753524323/5000000000 : ℝ)*X 0 2+(491723947/5000000000 : ℝ)*X 1 0+(5819805437/10000000000 : ℝ)*X 1 1+(2753524323/5000000000 : ℝ)*X 1 2+(491723947/5000000000 : ℝ)*X 2 0+(5819805437/10000000000 : ℝ)*X 2 1+(2753524323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209741397591030936998390493/58750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69635241/50000000000000 : ℝ)*(lower2) + (4007356987437511/100000000000000 : ℝ)*(major0) + (4007356987437511/100000000000000 : ℝ)*(major1) + (500919623429689/12500000000000 : ℝ)*(major2) + (2732884035478867/50000000000000 : ℝ)*(sp0) + (5465765326436067/100000000000000 : ℝ)*(sp1) + (5465768353701247/100000000000000 : ℝ)*(sp2) + (1274472168049809/50000000000000 : ℝ)*(sp3) + (3521321177/100000000000000 : ℝ)*(sp5) + (398627123/50000000000000 : ℝ)*(sp6) + (14917957/6250000000000 : ℝ)*(sp7) + (1079997759/100000000000000 : ℝ)*(sp8) + (303198249/100000000000000 : ℝ)*(sp9) + (130130379/100000000000000 : ℝ)*(sp11) + (2548944704917309/100000000000000 : ℝ)*(f.failure) + (5465769150955493/100000000000000 : ℝ)*(f.sum) + (70238909296933/18800000000000000000000000000 : ℝ)*base65 + (2489555173517412301/352500000000000000000000000000000 : ℝ)*base68 + (1797610714124420279/176250000000000000000000000000000 : ℝ)*base69 + (3654000499865087699/352500000000000000000000000000000 : ℝ)*base71 + (39986216576533/18800000000000000000000000000 : ℝ)*base73 + (1481408898078170279/176250000000000000000000000000000 : ℝ)*base75 + (11990663474984381449/352500000000000000000000000000000 : ℝ)*base77 + (12910170336881449/352500000000000000000000000000000 : ℝ)*base79 + (31381165281343/28200000000000000000000000000 : ℝ)*base81 + (10530953/10000000000000000000000 : ℝ)*base89 + (10530953/10000000000000000000000 : ℝ)*base91 + (89469047/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130149460673530709043118183/29375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56284893/100000000000000 : ℝ)*(lower4) + (4040052406378863/100000000000000 : ℝ)*(major0) + (4040052406378863/100000000000000 : ℝ)*(major1) + (252503275398679/6250000000000 : ℝ)*(major2) + (8715810667/100000000000000 : ℝ)*(sp1) + (571925809/25000000000000 : ℝ)*(sp3) + (4304969752213/78125000000 : ℝ)*(sp4) + (2755177127439013/50000000000000 : ℝ)*(sp5) + (5510361802283577/100000000000000 : ℝ)*(sp6) + (321217200645371/12500000000000 : ℝ)*(sp7) + (111169331/5000000000000 : ℝ)*(sp8) + (535530567/100000000000000 : ℝ)*(sp9) + (1703935683/100000000000000 : ℝ)*(sp10) + (316496231/25000000000000 : ℝ)*(sp11) + (321217644856391/12500000000000 : ℝ)*(f.failure) + (275518175310963/5000000000000 : ℝ)*(f.sum) + (301579248448351/56400000000000000000000000000 : ℝ)*base65 + (893733466048113067/352500000000000000000000000000000 : ℝ)*base67 + (110447887600105679/58750000000000000000000000000000 : ℝ)*base70 + (8987206706030613067/352500000000000000000000000000000 : ℝ)*base71 + (38769328180049/56400000000000000000000000000 : ℝ)*base74 + (317358021847394321/58750000000000000000000000000000 : ℝ)*base75 + (754795283159968939/117500000000000000000000000000000 : ℝ)*base77 + (804730298857468939/117500000000000000000000000000000 : ℝ)*base79 + (4703772135573/9400000000000000000000000000 : ℝ)*base81 + (568053/1250000000000000000000 : ℝ)*base90 + (568053/1250000000000000000000 : ℝ)*base92 + (13068053/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1405_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3969/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (187/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1405_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1405_s4_0 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1990583561/10000000000 : ℝ)*x 0 + (1352771771/2500000000 : ℝ)*x 1 + (524483749/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990583561/10000000000 : ℝ)^4365 ≤ (12137280025823/100000000000000 : ℝ)^3341 := by
    have hnat : (1990583561 : ℕ)^4365*100000000000000^3341 ≤ 12137280025823^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990583561 10000000000 12137280025823 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352771771/2500000000 : ℝ)^4365 ≤ (22413390168479/50000000000000 : ℝ)^3341 := by
    have hnat : (1352771771 : ℕ)^4365*50000000000000^3341 ≤ 22413390168479^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352771771 2500000000 22413390168479 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524483749/1000000000 : ℝ)^4365 ≤ (21517969807839/50000000000000 : ℝ)^3341 := by
    have hnat : (524483749 : ℕ)^4365*50000000000000^3341 ≤ 21517969807839^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524483749 1000000000 21517969807839 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1990583561/10000000000 : ℝ), (1352771771/2500000000 : ℝ), (524483749/1000000000 : ℝ)] ![(12137280025823/100000000000000 : ℝ), (22413390168479/50000000000000 : ℝ), (21517969807839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1990583561/10000000000 : ℝ)|^4365 ≤ (12137280025823/100000000000000 : ℝ)^3341
        have hw : |(-1990583561/10000000000 : ℝ)|=(1990583561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352771771/2500000000 : ℝ)|^4365 ≤ (22413390168479/50000000000000 : ℝ)^3341
        have hw : |(1352771771/2500000000 : ℝ)|=(1352771771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524483749/1000000000 : ℝ)|^4365 ≤ (21517969807839/50000000000000 : ℝ)^3341
        have hw : |(524483749/1000000000 : ℝ)|=(524483749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s4_1 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348241209/10000000000 : ℝ)*x 0 + (-2075271459/10000000000 : ℝ)*x 1 + (40975289/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348241209/10000000000 : ℝ)^4365 ≤ (22073896392719/50000000000000 : ℝ)^3341 := by
    have hnat : (5348241209 : ℕ)^4365*50000000000000^3341 ≤ 22073896392719^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348241209 10000000000 22073896392719 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075271459/10000000000 : ℝ)^4365 ≤ (6408136458557/50000000000000 : ℝ)^3341 := by
    have hnat : (2075271459 : ℕ)^4365*50000000000000^3341 ≤ 6408136458557^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075271459 10000000000 6408136458557 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40975289/78125000 : ℝ)^4365 ≤ (5379491784621/12500000000000 : ℝ)^3341 := by
    have hnat : (40975289 : ℕ)^4365*12500000000000^3341 ≤ 5379491784621^3341*78125000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40975289 78125000 5379491784621 12500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348241209/10000000000 : ℝ), (-2075271459/10000000000 : ℝ), (40975289/78125000 : ℝ)] ![(22073896392719/50000000000000 : ℝ), (6408136458557/50000000000000 : ℝ), (5379491784621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348241209/10000000000 : ℝ)|^4365 ≤ (22073896392719/50000000000000 : ℝ)^3341
        have hw : |(5348241209/10000000000 : ℝ)|=(5348241209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2075271459/10000000000 : ℝ)|^4365 ≤ (6408136458557/50000000000000 : ℝ)^3341
        have hw : |(-2075271459/10000000000 : ℝ)|=(2075271459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40975289/78125000 : ℝ)|^4365 ≤ (5379491784621/12500000000000 : ℝ)^3341
        have hw : |(40975289/78125000 : ℝ)|=(40975289/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s4_2 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069648293/2000000000 : ℝ)*x 0 + (524483661/1000000000 : ℝ)*x 1 + (-1037635813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069648293/2000000000 : ℝ)^4365 ≤ (44147795546307/100000000000000 : ℝ)^3341 := by
    have hnat : (1069648293 : ℕ)^4365*100000000000000^3341 ≤ 44147795546307^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069648293 2000000000 44147795546307 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524483661/1000000000 : ℝ)^4365 ≤ (10758982545453/25000000000000 : ℝ)^3341 := by
    have hnat : (524483661 : ℕ)^4365*25000000000000^3341 ≤ 10758982545453^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524483661 1000000000 10758982545453 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037635813/5000000000 : ℝ)^4365 ≤ (12816274264559/100000000000000 : ℝ)^3341 := by
    have hnat : (1037635813 : ℕ)^4365*100000000000000^3341 ≤ 12816274264559^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037635813 5000000000 12816274264559 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069648293/2000000000 : ℝ), (524483661/1000000000 : ℝ), (-1037635813/5000000000 : ℝ)] ![(44147795546307/100000000000000 : ℝ), (10758982545453/25000000000000 : ℝ), (12816274264559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069648293/2000000000 : ℝ)|^4365 ≤ (44147795546307/100000000000000 : ℝ)^3341
        have hw : |(1069648293/2000000000 : ℝ)|=(1069648293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524483661/1000000000 : ℝ)|^4365 ≤ (10758982545453/25000000000000 : ℝ)^3341
        have hw : |(524483661/1000000000 : ℝ)|=(524483661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037635813/5000000000 : ℝ)|^4365 ≤ (12816274264559/100000000000000 : ℝ)^3341
        have hw : |(-1037635813/5000000000 : ℝ)|=(1037635813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s4_3 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310300207/10000000000 : ℝ)*x 0 + (1033850439/2500000000 : ℝ)*x 1 + (4491896771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310300207/10000000000 : ℝ)^4365 ≤ (33303193364563/100000000000000 : ℝ)^3341 := by
    have hnat : (4310300207 : ℕ)^4365*100000000000000^3341 ≤ 33303193364563^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310300207 10000000000 33303193364563 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033850439/2500000000 : ℝ)^4365 ≤ (15774379449969/50000000000000 : ℝ)^3341 := by
    have hnat : (1033850439 : ℕ)^4365*50000000000000^3341 ≤ 15774379449969^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033850439 2500000000 15774379449969 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491896771/10000000000 : ℝ)^4365 ≤ (35148047711319/100000000000000 : ℝ)^3341 := by
    have hnat : (4491896771 : ℕ)^4365*100000000000000^3341 ≤ 35148047711319^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491896771 10000000000 35148047711319 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310300207/10000000000 : ℝ), (1033850439/2500000000 : ℝ), (4491896771/10000000000 : ℝ)] ![(33303193364563/100000000000000 : ℝ), (15774379449969/50000000000000 : ℝ), (35148047711319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310300207/10000000000 : ℝ)|^4365 ≤ (33303193364563/100000000000000 : ℝ)^3341
        have hw : |(4310300207/10000000000 : ℝ)|=(4310300207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033850439/2500000000 : ℝ)|^4365 ≤ (15774379449969/50000000000000 : ℝ)^3341
        have hw : |(1033850439/2500000000 : ℝ)|=(1033850439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491896771/10000000000 : ℝ)|^4365 ≤ (35148047711319/100000000000000 : ℝ)^3341
        have hw : |(4491896771/10000000000 : ℝ)|=(4491896771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s4_4 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1990596017/10000000000 : ℝ)*x 0 + (5245446659/10000000000 : ℝ)*x 1 + (216418981/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990596017/10000000000 : ℝ)^4365 ≤ (606868962617/5000000000000 : ℝ)^3341 := by
    have hnat : (1990596017 : ℕ)^4365*5000000000000^3341 ≤ 606868962617^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990596017 10000000000 606868962617 5000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245446659/10000000000 : ℝ)^4365 ≤ (21521235103823/50000000000000 : ℝ)^3341 := by
    have hnat : (5245446659 : ℕ)^4365*50000000000000^3341 ≤ 21521235103823^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245446659 10000000000 21521235103823 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216418981/400000000 : ℝ)^4365 ≤ (44820150525367/100000000000000 : ℝ)^3341 := by
    have hnat : (216418981 : ℕ)^4365*100000000000000^3341 ≤ 44820150525367^3341*400000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216418981 400000000 44820150525367 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1990596017/10000000000 : ℝ), (5245446659/10000000000 : ℝ), (216418981/400000000 : ℝ)] ![(606868962617/5000000000000 : ℝ), (21521235103823/50000000000000 : ℝ), (44820150525367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1990596017/10000000000 : ℝ)|^4365 ≤ (606868962617/5000000000000 : ℝ)^3341
        have hw : |(-1990596017/10000000000 : ℝ)|=(1990596017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245446659/10000000000 : ℝ)|^4365 ≤ (21521235103823/50000000000000 : ℝ)^3341
        have hw : |(5245446659/10000000000 : ℝ)|=(5245446659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216418981/400000000 : ℝ)|^4365 ≤ (44820150525367/100000000000000 : ℝ)^3341
        have hw : |(216418981/400000000 : ℝ)|=(216418981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s4_5 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265256231/500000000 : ℝ)*x 0 + (-3819267/20000000 : ℝ)*x 1 + (5410474671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265256231/500000000 : ℝ)^4365 ≤ (10920842828441/25000000000000 : ℝ)^3341 := by
    have hnat : (265256231 : ℕ)^4365*25000000000000^3341 ≤ 10920842828441^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265256231 500000000 10920842828441 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3819267/20000000 : ℝ)^4365 ≤ (5748238283531/50000000000000 : ℝ)^3341 := by
    have hnat : (3819267 : ℕ)^4365*50000000000000^3341 ≤ 5748238283531^3341*20000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3819267 20000000 5748238283531 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410474671/10000000000 : ℝ)^4365 ≤ (22410076052759/50000000000000 : ℝ)^3341 := by
    have hnat : (5410474671 : ℕ)^4365*50000000000000^3341 ≤ 22410076052759^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410474671 10000000000 22410076052759 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265256231/500000000 : ℝ), (-3819267/20000000 : ℝ), (5410474671/10000000000 : ℝ)] ![(10920842828441/25000000000000 : ℝ), (5748238283531/50000000000000 : ℝ), (22410076052759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265256231/500000000 : ℝ)|^4365 ≤ (10920842828441/25000000000000 : ℝ)^3341
        have hw : |(265256231/500000000 : ℝ)|=(265256231/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3819267/20000000 : ℝ)|^4365 ≤ (5748238283531/50000000000000 : ℝ)^3341
        have hw : |(-3819267/20000000 : ℝ)|=(3819267/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410474671/10000000000 : ℝ)|^4365 ≤ (22410076052759/50000000000000 : ℝ)^3341
        have hw : |(5410474671/10000000000 : ℝ)|=(5410474671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s4_6 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652562299/5000000000 : ℝ)*x 0 + (5410474589/10000000000 : ℝ)*x 1 + (-1909633643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652562299/5000000000 : ℝ)^4365 ≤ (4368337107709/10000000000000 : ℝ)^3341 := by
    have hnat : (2652562299 : ℕ)^4365*10000000000000^3341 ≤ 4368337107709^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652562299 5000000000 4368337107709 10000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410474589/10000000000 : ℝ)^4365 ≤ (11205037804509/25000000000000 : ℝ)^3341 := by
    have hnat : (5410474589 : ℕ)^4365*25000000000000^3341 ≤ 11205037804509^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410474589 10000000000 11205037804509 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1909633643/10000000000 : ℝ)^4365 ≤ (5748238845909/50000000000000 : ℝ)^3341 := by
    have hnat : (1909633643 : ℕ)^4365*50000000000000^3341 ≤ 5748238845909^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909633643 10000000000 5748238845909 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652562299/5000000000 : ℝ), (5410474589/10000000000 : ℝ), (-1909633643/10000000000 : ℝ)] ![(4368337107709/10000000000000 : ℝ), (11205037804509/25000000000000 : ℝ), (5748238845909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652562299/5000000000 : ℝ)|^4365 ≤ (4368337107709/10000000000000 : ℝ)^3341
        have hw : |(2652562299/5000000000 : ℝ)|=(2652562299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410474589/10000000000 : ℝ)|^4365 ≤ (11205037804509/25000000000000 : ℝ)^3341
        have hw : |(5410474589/10000000000 : ℝ)|=(5410474589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1909633643/10000000000 : ℝ)|^4365 ≤ (5748238845909/50000000000000 : ℝ)^3341
        have hw : |(-1909633643/10000000000 : ℝ)|=(1909633643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s4_7 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269395367/625000000 : ℝ)*x 0 + (898117933/2000000000 : ℝ)*x 1 + (4136716297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269395367/625000000 : ℝ)^4365 ≤ (33303452440929/100000000000000 : ℝ)^3341 := by
    have hnat : (269395367 : ℕ)^4365*100000000000000^3341 ≤ 33303452440929^3341*625000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269395367 625000000 33303452440929 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898117933/2000000000 : ℝ)^4365 ≤ (17567342868201/50000000000000 : ℝ)^3341 := by
    have hnat : (898117933 : ℕ)^4365*50000000000000^3341 ≤ 17567342868201^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898117933 2000000000 17567342868201 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4136716297/10000000000 : ℝ)^4365 ≤ (31561861806191/100000000000000 : ℝ)^3341 := by
    have hnat : (4136716297 : ℕ)^4365*100000000000000^3341 ≤ 31561861806191^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136716297 10000000000 31561861806191 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269395367/625000000 : ℝ), (898117933/2000000000 : ℝ), (4136716297/10000000000 : ℝ)] ![(33303452440929/100000000000000 : ℝ), (17567342868201/50000000000000 : ℝ), (31561861806191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269395367/625000000 : ℝ)|^4365 ≤ (33303452440929/100000000000000 : ℝ)^3341
        have hw : |(269395367/625000000 : ℝ)|=(269395367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898117933/2000000000 : ℝ)|^4365 ≤ (17567342868201/50000000000000 : ℝ)^3341
        have hw : |(898117933/2000000000 : ℝ)|=(898117933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4136716297/10000000000 : ℝ)|^4365 ≤ (31561861806191/100000000000000 : ℝ)^3341
        have hw : |(4136716297/10000000000 : ℝ)|=(4136716297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1405_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (187/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5629/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7389/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (187/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (187/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (187/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (187/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (187/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (187/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11087/100000 : ℝ) ^ (1091/256 : ℝ) ≤ (1699401950102551/20000000000000000000 : ℝ) := by
    have hpowers : (11087/100000 : ℝ)^1091 ≤ (1699401950102551/20000000000000000000 : ℝ)^256 := by
      have hnat : (11087 : ℕ)^1091*20000000000000000000^256 ≤ 1699401950102551^256*100000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11087 100000 1699401950102551 20000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11087/100000 : ℝ)) (X := (1699401950102551/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hpowhi : (187/1250 : ℝ) ^ (1091/256 : ℝ) ≤ (30464250801091937/100000000000000000000 : ℝ) := by
    have hpowers : (187/1250 : ℝ)^1091 ≤ (30464250801091937/100000000000000000000 : ℝ)^256 := by
      have hnat : (187 : ℕ)^1091*100000000000000000000^256 ≤ 30464250801091937^256*1250^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        187 1250 30464250801091937 100000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (187/1250 : ℝ)) (X := (30464250801091937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001699401950102551/10000000000000000000 : ℝ) ≤ (5000199366915691/5000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (10001699401950102551/10000000000000000000 : ℝ)^256 ≤ (5000199366915691/5000000000000000 : ℝ)^1091 := by
      have hnat : (10001699401950102551 : ℕ)^256*5000000000000000^1091 ≤ 5000199366915691^1091*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001699401950102551 10000000000000000000 5000199366915691 5000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000199366915691/5000000000000000 : ℝ)) (X := (10001699401950102551/10000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009740315137901173/25000000000000000000 : ℝ) ≤ (10000914078455597/10000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (25009740315137901173/25000000000000000000 : ℝ)^256 ≤ (10000914078455597/10000000000000000 : ℝ)^1091 := by
      have hnat : (25009740315137901173 : ℕ)^256*10000000000000000^1091 ≤ 10000914078455597^1091*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009740315137901173 25000000000000000000 10000914078455597 10000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000914078455597/10000000000000000 : ℝ)) (X := (25009740315137901173/25000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030464250801091937/50000000000000000000 : ℝ) ≤ (2500357355769953/2500000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (50030464250801091937/50000000000000000000 : ℝ)^256 ≤ (2500357355769953/2500000000000000 : ℝ)^1091 := by
      have hnat : (50030464250801091937 : ℕ)^256*2500000000000000^1091 ≤ 2500357355769953^1091*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030464250801091937 50000000000000000000 2500357355769953 2500000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500357355769953/2500000000000000 : ℝ)) (X := (50030464250801091937/50000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1699401950102551/20000000000000000000 : ℝ) ≤ ((3226676420369299923/3227500000000000000 : ℝ)+2*(34356308281/25820000000000 : ℝ)*(11087/100000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (3226676420369299923/3227500000000000000 : ℝ)+2*(34356308281/25820000000000 : ℝ)*(11087/100000 : ℝ)=(5000199366915691/5000000000000000 : ℝ) by norm_num, show 1+2*(1699401950102551/20000000000000000000 : ℝ)=(10001699401950102551/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30464250801091937/100000000000000000000 : ℝ)+(1699401950102551/20000000000000000000 : ℝ) ≤ ((3226676420369299923/3227500000000000000 : ℝ)+(34356308281/25820000000000 : ℝ)*((187/1250 : ℝ)+(11087/100000 : ℝ)))^(1091/256 : ℝ) := by
    rw [show (3226676420369299923/3227500000000000000 : ℝ)+(34356308281/25820000000000 : ℝ)*((187/1250 : ℝ)+(11087/100000 : ℝ))=(10000914078455597/10000000000000000 : ℝ) by norm_num, show 1+(30464250801091937/100000000000000000000 : ℝ)+(1699401950102551/20000000000000000000 : ℝ)=(25009740315137901173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30464250801091937/100000000000000000000 : ℝ) ≤ ((3226676420369299923/3227500000000000000 : ℝ)+2*(34356308281/25820000000000 : ℝ)*(187/1250 : ℝ))^(1091/256 : ℝ) := by
    rw [show (3226676420369299923/3227500000000000000 : ℝ)+2*(34356308281/25820000000000 : ℝ)*(187/1250 : ℝ)=(2500357355769953/2500000000000000 : ℝ) by norm_num, show 1+2*(30464250801091937/100000000000000000000 : ℝ)=(50030464250801091937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3226676420369299923/3227500000000000000 : ℝ)*(X 1 0+X 2 0)+(34356308281/25820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (187/1250 : ℝ)) (c := (3226676420369299923/3227500000000000000 : ℝ)) (alpha := (34356308281/25820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3226676420369299923/3227500000000000000 : ℝ)*(X 0 1+X 2 1)+(34356308281/25820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (187/1250 : ℝ)) (c := (3226676420369299923/3227500000000000000 : ℝ)) (alpha := (34356308281/25820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3226676420369299923/3227500000000000000 : ℝ)*(X 0 2+X 1 2)+(34356308281/25820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (187/1250 : ℝ)) (c := (3226676420369299923/3227500000000000000 : ℝ)) (alpha := (34356308281/25820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1990583561/10000000000 : ℝ)*X 0 0+(1352771771/2500000000 : ℝ)*X 0 1+(524483749/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348241209/10000000000 : ℝ)*X 1 0+(-2075271459/10000000000 : ℝ)*X 1 1+(40975289/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069648293/2000000000 : ℝ)*X 2 0+(524483661/1000000000 : ℝ)*X 2 1+(-1037635813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310300207/10000000000 : ℝ)*X 0 0+(1033850439/2500000000 : ℝ)*X 0 1+(4491896771/10000000000 : ℝ)*X 0 2+(4310300207/10000000000 : ℝ)*X 1 0+(1033850439/2500000000 : ℝ)*X 1 1+(4491896771/10000000000 : ℝ)*X 1 2+(4310300207/10000000000 : ℝ)*X 2 0+(1033850439/2500000000 : ℝ)*X 2 1+(4491896771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1990596017/10000000000 : ℝ)*X 0 0+(5245446659/10000000000 : ℝ)*X 0 1+(216418981/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265256231/500000000 : ℝ)*X 1 0+(-3819267/20000000 : ℝ)*X 1 1+(5410474671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652562299/5000000000 : ℝ)*X 2 0+(5410474589/10000000000 : ℝ)*X 2 1+(-1909633643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269395367/625000000 : ℝ)*X 0 0+(898117933/2000000000 : ℝ)*X 0 1+(4136716297/10000000000 : ℝ)*X 0 2+(269395367/625000000 : ℝ)*X 1 0+(898117933/2000000000 : ℝ)*X 1 1+(4136716297/10000000000 : ℝ)*X 1 2+(269395367/625000000 : ℝ)*X 2 0+(898117933/2000000000 : ℝ)*X 2 1+(4136716297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188782999610656912385144853/40343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (505993203/100000000000000 : ℝ)*(base19) + (145024973/100000000000000 : ℝ)*(base23) + (485533/195312500000 : ℝ)*(lower2) + (24360761/10000000000000 : ℝ)*(upper5) + (1102516265908371/25000000000000 : ℝ)*(major0) + (1102516265908371/25000000000000 : ℝ)*(major1) + (1102516265908371/25000000000000 : ℝ)*(major2) + (6015036233064177/100000000000000 : ℝ)*(sp0) + (6015032168654191/100000000000000 : ℝ)*(sp1) + (1203001939430963/20000000000000 : ℝ)*(sp2) + (350636448664849/12500000000000 : ℝ)*(sp3) + (3558416783/100000000000000 : ℝ)*(sp5) + (26390884389/100000000000000 : ℝ)*(sp6) + (429781053/20000000000000 : ℝ)*(sp7) + (2805093738224057/100000000000000 : ℝ)*(f.failure) + (6015036233064177/100000000000000 : ℝ)*(f.sum) + (5491656958553/1291000000000000000000000000 : ℝ)*base66 + (1097354392410792933/80687500000000000000000000000000 : ℝ)*base67 + (1436407687310667933/80687500000000000000000000000000 : ℝ)*base69 + (178510513949667933/80687500000000000000000000000000 : ℝ)*base71 + (1340539227219/322750000000000000000000000 : ℝ)*base73 + (307602380730355433/80687500000000000000000000000000 : ℝ)*base75 + (1544206949484792933/80687500000000000000000000000000 : ℝ)*base77 + (890529866268730433/80687500000000000000000000000000 : ℝ)*base79 + (135040019713/40343750000000000000000000 : ℝ)*base82 + (37661931/10000000000000000000000 : ℝ)*base90 + (37661931/10000000000000000000000 : ℝ)*base92 + (37661931/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (203862728495808892647396261/80687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (548061/200000000000 : ℝ)*(base19) + (31899703/10000000000000 : ℝ)*(base23) + (29656201/50000000000000 : ℝ)*(upper2) + (39272911/100000000000000 : ℝ)*(upper3) + (25696477/25000000000000 : ℝ)*(upper5) + (2221362813192123/50000000000000 : ℝ)*(major0) + (2221362813192123/50000000000000 : ℝ)*(major1) + (2221362813192123/50000000000000 : ℝ)*(major2) + (10563055217/100000000000000 : ℝ)*(sp1) + (2715674653/50000000000000 : ℝ)*(sp2) + (3029791573619753/50000000000000 : ℝ)*(sp4) + (6059572310153789/100000000000000 : ℝ)*(sp5) + (605957739689317/10000000000000 : ℝ)*(sp6) + (282586802130993/10000000000000 : ℝ)*(sp7) + (282586802130993/10000000000000 : ℝ)*(f.failure) + (3029791573619753/50000000000000 : ℝ)*(f.sum) + (1025848568013/322750000000000000000000000 : ℝ)*base66 + (2613255769279518471/161375000000000000000000000000000 : ℝ)*base68 + (2394613615929018471/161375000000000000000000000000000 : ℝ)*base70 + (1020346961454393471/161375000000000000000000000000000 : ℝ)*base72 + (4996158196851/1291000000000000000000000000 : ℝ)*base74 + (2535458655129393471/161375000000000000000000000000000 : ℝ)*base76 + (2259924239497768471/161375000000000000000000000000000 : ℝ)*base78 + (1615803242126518471/161375000000000000000000000000000 : ℝ)*base80 + (2408373315989/645500000000000000000000000 : ℝ)*base82 + (11012781/1000000000000000000000 : ℝ)*base89 + (11012781/1000000000000000000000 : ℝ)*base91 + (11012781/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1405_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (187/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1405_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1405_s5_0 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-995372263/5000000000 : ℝ)*x 0 + (2704838287/5000000000 : ℝ)*x 1 + (1311535459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (995372263/5000000000 : ℝ)^4365 ≤ (12138562313789/100000000000000 : ℝ)^3341 := by
    have hnat : (995372263 : ℕ)^4365*100000000000000^3341 ≤ 12138562313789^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995372263 5000000000 12138562313789 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704838287/5000000000 : ℝ)^4365 ≤ (22405757267653/50000000000000 : ℝ)^3341 := by
    have hnat : (2704838287 : ℕ)^4365*50000000000000^3341 ≤ 22405757267653^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704838287 5000000000 22405757267653 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311535459/2500000000 : ℝ)^4365 ≤ (43049923131773/100000000000000 : ℝ)^3341 := by
    have hnat : (1311535459 : ℕ)^4365*100000000000000^3341 ≤ 43049923131773^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311535459 2500000000 43049923131773 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-995372263/5000000000 : ℝ), (2704838287/5000000000 : ℝ), (1311535459/2500000000 : ℝ)] ![(12138562313789/100000000000000 : ℝ), (22405757267653/50000000000000 : ℝ), (43049923131773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-995372263/5000000000 : ℝ)|^4365 ≤ (12138562313789/100000000000000 : ℝ)^3341
        have hw : |(-995372263/5000000000 : ℝ)|=(995372263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704838287/5000000000 : ℝ)|^4365 ≤ (22405757267653/50000000000000 : ℝ)^3341
        have hw : |(2704838287/5000000000 : ℝ)|=(2704838287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311535459/2500000000 : ℝ)|^4365 ≤ (43049923131773/100000000000000 : ℝ)^3341
        have hw : |(1311535459/2500000000 : ℝ)|=(1311535459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s5_1 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668484723/1250000000 : ℝ)*x 0 + (-1037011807/5000000000 : ℝ)*x 1 + (2623070819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668484723/1250000000 : ℝ)^4365 ≤ (8828774683459/20000000000000 : ℝ)^3341 := by
    have hnat : (668484723 : ℕ)^4365*20000000000000^3341 ≤ 8828774683459^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668484723 1250000000 8828774683459 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037011807/5000000000 : ℝ)^4365 ≤ (6403102782913/50000000000000 : ℝ)^3341 := by
    have hnat : (1037011807 : ℕ)^4365*50000000000000^3341 ≤ 6403102782913^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037011807 5000000000 6403102782913 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623070819/5000000000 : ℝ)^4365 ≤ (43049921008991/100000000000000 : ℝ)^3341 := by
    have hnat : (2623070819 : ℕ)^4365*100000000000000^3341 ≤ 43049921008991^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623070819 5000000000 43049921008991 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668484723/1250000000 : ℝ), (-1037011807/5000000000 : ℝ), (2623070819/5000000000 : ℝ)] ![(8828774683459/20000000000000 : ℝ), (6403102782913/50000000000000 : ℝ), (43049921008991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668484723/1250000000 : ℝ)|^4365 ≤ (8828774683459/20000000000000 : ℝ)^3341
        have hw : |(668484723/1250000000 : ℝ)|=(668484723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1037011807/5000000000 : ℝ)|^4365 ≤ (6403102782913/50000000000000 : ℝ)^3341
        have hw : |(-1037011807/5000000000 : ℝ)|=(1037011807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623070819/5000000000 : ℝ)|^4365 ≤ (43049921008991/100000000000000 : ℝ)^3341
        have hw : |(2623070819/5000000000 : ℝ)|=(2623070819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s5_2 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20890147/39062500 : ℝ)*x 0 + (262307081/500000000 : ℝ)*x 1 + (-2074023841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20890147/39062500 : ℝ)^4365 ≤ (44143871778063/100000000000000 : ℝ)^3341 := by
    have hnat : (20890147 : ℕ)^4365*100000000000000^3341 ≤ 44143871778063^3341*39062500^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20890147 39062500 44143871778063 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262307081/500000000 : ℝ)^4365 ≤ (43049920816011/100000000000000 : ℝ)^3341 := by
    have hnat : (262307081 : ℕ)^4365*100000000000000^3341 ≤ 43049920816011^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262307081 500000000 43049920816011 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074023841/10000000000 : ℝ)^4365 ≤ (2561241479409/20000000000000 : ℝ)^3341 := by
    have hnat : (2074023841 : ℕ)^4365*20000000000000^3341 ≤ 2561241479409^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074023841 10000000000 2561241479409 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20890147/39062500 : ℝ), (262307081/500000000 : ℝ), (-2074023841/10000000000 : ℝ)] ![(44143871778063/100000000000000 : ℝ), (43049920816011/100000000000000 : ℝ), (2561241479409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20890147/39062500 : ℝ)|^4365 ≤ (44143871778063/100000000000000 : ℝ)^3341
        have hw : |(20890147/39062500 : ℝ)|=(20890147/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262307081/500000000 : ℝ)|^4365 ≤ (43049920816011/100000000000000 : ℝ)^3341
        have hw : |(262307081/500000000 : ℝ)|=(262307081/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074023841/10000000000 : ℝ)|^4365 ≤ (2561241479409/20000000000000 : ℝ)^3341
        have hw : |(-2074023841/10000000000 : ℝ)|=(2074023841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s5_3 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2155197833/5000000000 : ℝ)*x 0 + (1034575719/2500000000 : ℝ)*x 1 + (22444867/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155197833/5000000000 : ℝ)^4365 ≤ (33304156981637/100000000000000 : ℝ)^3341 := by
    have hnat : (2155197833 : ℕ)^4365*100000000000000^3341 ≤ 33304156981637^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155197833 5000000000 33304156981637 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034575719/2500000000 : ℝ)^4365 ≤ (31577677996201/100000000000000 : ℝ)^3341 := by
    have hnat : (1034575719 : ℕ)^4365*100000000000000^3341 ≤ 31577677996201^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034575719 2500000000 31577677996201 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22444867/50000000 : ℝ)^4365 ≤ (35118165012071/100000000000000 : ℝ)^3341 := by
    have hnat : (22444867 : ℕ)^4365*100000000000000^3341 ≤ 35118165012071^3341*50000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22444867 50000000 35118165012071 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155197833/5000000000 : ℝ), (1034575719/2500000000 : ℝ), (22444867/50000000 : ℝ)] ![(33304156981637/100000000000000 : ℝ), (31577677996201/100000000000000 : ℝ), (35118165012071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155197833/5000000000 : ℝ)|^4365 ≤ (33304156981637/100000000000000 : ℝ)^3341
        have hw : |(2155197833/5000000000 : ℝ)|=(2155197833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034575719/2500000000 : ℝ)|^4365 ≤ (31577677996201/100000000000000 : ℝ)^3341
        have hw : |(1034575719/2500000000 : ℝ)|=(1034575719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22444867/50000000 : ℝ)|^4365 ≤ (35118165012071/100000000000000 : ℝ)^3341
        have hw : |(22444867/50000000 : ℝ)|=(22444867/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s5_4 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1990756723/10000000000 : ℝ)*x 0 + (2623365959/5000000000 : ℝ)*x 1 + (270454151/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990756723/10000000000 : ℝ)^4365 ≤ (3034664869869/25000000000000 : ℝ)^3341 := by
    have hnat : (1990756723 : ℕ)^4365*25000000000000^3341 ≤ 3034664869869^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990756723 10000000000 3034664869869 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623365959/5000000000 : ℝ)^4365 ≤ (21528124790139/50000000000000 : ℝ)^3341 := by
    have hnat : (2623365959 : ℕ)^4365*50000000000000^3341 ≤ 21528124790139^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623365959 5000000000 21528124790139 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270454151/500000000 : ℝ)^4365 ≤ (896101818547/2000000000000 : ℝ)^3341 := by
    have hnat : (270454151 : ℕ)^4365*2000000000000^3341 ≤ 896101818547^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270454151 500000000 896101818547 2000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1990756723/10000000000 : ℝ), (2623365959/5000000000 : ℝ), (270454151/500000000 : ℝ)] ![(3034664869869/25000000000000 : ℝ), (21528124790139/50000000000000 : ℝ), (896101818547/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1990756723/10000000000 : ℝ)|^4365 ≤ (3034664869869/25000000000000 : ℝ)^3341
        have hw : |(-1990756723/10000000000 : ℝ)|=(1990756723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623365959/5000000000 : ℝ)|^4365 ≤ (21528124790139/50000000000000 : ℝ)^3341
        have hw : |(2623365959/5000000000 : ℝ)|=(2623365959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270454151/500000000 : ℝ)|^4365 ≤ (896101818547/2000000000000 : ℝ)^3341
        have hw : |(270454151/500000000 : ℝ)|=(270454151/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s5_5 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165795781/312500000 : ℝ)*x 0 + (-23888533/125000000 : ℝ)*x 1 + (270454151/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165795781/312500000 : ℝ)^4365 ≤ (43687033044681/100000000000000 : ℝ)^3341 := by
    have hnat : (165795781 : ℕ)^4365*100000000000000^3341 ≤ 43687033044681^3341*312500000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165795781 312500000 43687033044681 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23888533/125000000 : ℝ)^4365 ≤ (287696900063/2500000000000 : ℝ)^3341 := by
    have hnat : (23888533 : ℕ)^4365*2500000000000^3341 ≤ 287696900063^3341*125000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23888533 125000000 287696900063 2500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270454151/500000000 : ℝ)^4365 ≤ (896101818547/2000000000000 : ℝ)^3341 := by
    have hnat : (270454151 : ℕ)^4365*2000000000000^3341 ≤ 896101818547^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270454151 500000000 896101818547 2000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165795781/312500000 : ℝ), (-23888533/125000000 : ℝ), (270454151/500000000 : ℝ)] ![(43687033044681/100000000000000 : ℝ), (287696900063/2500000000000 : ℝ), (896101818547/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165795781/312500000 : ℝ)|^4365 ≤ (43687033044681/100000000000000 : ℝ)^3341
        have hw : |(165795781/312500000 : ℝ)|=(165795781/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23888533/125000000 : ℝ)|^4365 ≤ (287696900063/2500000000000 : ℝ)^3341
        have hw : |(-23888533/125000000 : ℝ)|=(23888533/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270454151/500000000 : ℝ)|^4365 ≤ (896101818547/2000000000000 : ℝ)^3341
        have hw : |(270454151/500000000 : ℝ)|=(270454151/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s5_6 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530546499/1000000000 : ℝ)*x 0 + (2704541511/5000000000 : ℝ)*x 1 + (-23888533/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530546499/1000000000 : ℝ)^4365 ≤ (8737406604633/20000000000000 : ℝ)^3341 := by
    have hnat : (530546499 : ℕ)^4365*20000000000000^3341 ≤ 8737406604633^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530546499 1000000000 8737406604633 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704541511/5000000000 : ℝ)^4365 ≤ (22402545474497/50000000000000 : ℝ)^3341 := by
    have hnat : (2704541511 : ℕ)^4365*50000000000000^3341 ≤ 22402545474497^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704541511 5000000000 22402545474497 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23888533/125000000 : ℝ)^4365 ≤ (287696900063/2500000000000 : ℝ)^3341 := by
    have hnat : (23888533 : ℕ)^4365*2500000000000^3341 ≤ 287696900063^3341*125000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23888533 125000000 287696900063 2500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530546499/1000000000 : ℝ), (2704541511/5000000000 : ℝ), (-23888533/125000000 : ℝ)] ![(8737406604633/20000000000000 : ℝ), (22402545474497/50000000000000 : ℝ), (287696900063/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530546499/1000000000 : ℝ)|^4365 ≤ (8737406604633/20000000000000 : ℝ)^3341
        have hw : |(530546499/1000000000 : ℝ)|=(530546499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704541511/5000000000 : ℝ)|^4365 ≤ (22402545474497/50000000000000 : ℝ)^3341
        have hw : |(2704541511/5000000000 : ℝ)|=(2704541511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23888533/125000000 : ℝ)|^4365 ≤ (287696900063/2500000000000 : ℝ)^3341
        have hw : |(-23888533/125000000 : ℝ)|=(23888533/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s5_7 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (862084277/2000000000 : ℝ)*x 0 + (2243853953/5000000000 : ℝ)*x 1 + (1034893539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862084277/2000000000 : ℝ)^4365 ≤ (33304416604871/100000000000000 : ℝ)^3341 := by
    have hnat : (862084277 : ℕ)^4365*100000000000000^3341 ≤ 33304416604871^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862084277 2000000000 33304416604871 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243853953/5000000000 : ℝ)^4365 ≤ (1097038468173/3125000000000 : ℝ)^3341 := by
    have hnat : (2243853953 : ℕ)^4365*3125000000000^3341 ≤ 1097038468173^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243853953 5000000000 1097038468173 3125000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034893539/2500000000 : ℝ)^4365 ≤ (1579517619723/5000000000000 : ℝ)^3341 := by
    have hnat : (1034893539 : ℕ)^4365*5000000000000^3341 ≤ 1579517619723^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034893539 2500000000 1579517619723 5000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862084277/2000000000 : ℝ), (2243853953/5000000000 : ℝ), (1034893539/2500000000 : ℝ)] ![(33304416604871/100000000000000 : ℝ), (1097038468173/3125000000000 : ℝ), (1579517619723/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862084277/2000000000 : ℝ)|^4365 ≤ (33304416604871/100000000000000 : ℝ)^3341
        have hw : |(862084277/2000000000 : ℝ)|=(862084277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243853953/5000000000 : ℝ)|^4365 ≤ (1097038468173/3125000000000 : ℝ)^3341
        have hw : |(2243853953/5000000000 : ℝ)|=(2243853953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034893539/2500000000 : ℝ)|^4365 ≤ (1579517619723/5000000000000 : ℝ)^3341
        have hw : |(1034893539/2500000000 : ℝ)|=(1034893539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1405_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5643/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5629/50000 : ℝ) ^ (1091/256 : ℝ) ≤ (9069735038186589/100000000000000000000 : ℝ) := by
    have hpowers : (5629/50000 : ℝ)^1091 ≤ (9069735038186589/100000000000000000000 : ℝ)^256 := by
      have hnat : (5629 : ℕ)^1091*100000000000000000000^256 ≤ 9069735038186589^256*50000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5629 50000 9069735038186589 100000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5629/50000 : ℝ)) (X := (9069735038186589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7389/50000 : ℝ) ^ (1091/256 : ℝ) ≤ (1445790951307349/5000000000000000000 : ℝ) := by
    have hpowers : (7389/50000 : ℝ)^1091 ≤ (1445790951307349/5000000000000000000 : ℝ)^256 := by
      have hnat : (7389 : ℕ)^1091*5000000000000000000^256 ≤ 1445790951307349^256*50000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7389 50000 1445790951307349 5000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7389/50000 : ℝ)) (X := (1445790951307349/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009069735038186589/50000000000000000000 : ℝ) ≤ (2000085121577067/2000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (50009069735038186589/50000000000000000000 : ℝ)^256 ≤ (2000085121577067/2000000000000000 : ℝ)^1091 := by
      have hnat : (50009069735038186589 : ℕ)^256*2000000000000000^1091 ≤ 2000085121577067^1091*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009069735038186589 50000000000000000000 2000085121577067 2000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000085121577067/2000000000000000 : ℝ)) (X := (50009069735038186589/50000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037985554064333569/100000000000000000000 : ℝ) ≤ (50004455952619/50000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (100037985554064333569/100000000000000000000 : ℝ)^256 ≤ (50004455952619/50000000000000 : ℝ)^1091 := by
      have hnat : (100037985554064333569 : ℕ)^256*50000000000000^1091 ≤ 50004455952619^1091*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037985554064333569 100000000000000000000 50004455952619 50000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50004455952619/50000000000000 : ℝ)) (X := (100037985554064333569/100000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501445790951307349/2500000000000000000 : ℝ) ≤ (2000271354632453/2000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (2501445790951307349/2500000000000000000 : ℝ)^256 ≤ (2000271354632453/2000000000000000 : ℝ)^1091 := by
      have hnat : (2501445790951307349 : ℕ)^256*2000000000000000^1091 ≤ 2000271354632453^1091*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501445790951307349 2500000000000000000 2000271354632453 2000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000271354632453/2000000000000000 : ℝ)) (X := (2501445790951307349/2500000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9069735038186589/100000000000000000000 : ℝ) ≤ ((1759550754053435063/1760000000000000000 : ℝ)+2*(93116527693/70400000000000 : ℝ)*(5629/50000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (1759550754053435063/1760000000000000000 : ℝ)+2*(93116527693/70400000000000 : ℝ)*(5629/50000 : ℝ)=(2000085121577067/2000000000000000 : ℝ) by norm_num, show 1+2*(9069735038186589/100000000000000000000 : ℝ)=(50009069735038186589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1445790951307349/5000000000000000000 : ℝ)+(9069735038186589/100000000000000000000 : ℝ) ≤ ((1759550754053435063/1760000000000000000 : ℝ)+(93116527693/70400000000000 : ℝ)*((7389/50000 : ℝ)+(5629/50000 : ℝ)))^(1091/256 : ℝ) := by
    rw [show (1759550754053435063/1760000000000000000 : ℝ)+(93116527693/70400000000000 : ℝ)*((7389/50000 : ℝ)+(5629/50000 : ℝ))=(50004455952619/50000000000000 : ℝ) by norm_num, show 1+(1445790951307349/5000000000000000000 : ℝ)+(9069735038186589/100000000000000000000 : ℝ)=(100037985554064333569/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1445790951307349/5000000000000000000 : ℝ) ≤ ((1759550754053435063/1760000000000000000 : ℝ)+2*(93116527693/70400000000000 : ℝ)*(7389/50000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (1759550754053435063/1760000000000000000 : ℝ)+2*(93116527693/70400000000000 : ℝ)*(7389/50000 : ℝ)=(2000271354632453/2000000000000000 : ℝ) by norm_num, show 1+2*(1445790951307349/5000000000000000000 : ℝ)=(2501445790951307349/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1759550754053435063/1760000000000000000 : ℝ)*(X 1 0+X 2 0)+(93116527693/70400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (1759550754053435063/1760000000000000000 : ℝ)) (alpha := (93116527693/70400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1759550754053435063/1760000000000000000 : ℝ)*(X 0 1+X 2 1)+(93116527693/70400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (1759550754053435063/1760000000000000000 : ℝ)) (alpha := (93116527693/70400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1759550754053435063/1760000000000000000 : ℝ)*(X 0 2+X 1 2)+(93116527693/70400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (1759550754053435063/1760000000000000000 : ℝ)) (alpha := (93116527693/70400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-995372263/5000000000 : ℝ)*X 0 0+(2704838287/5000000000 : ℝ)*X 0 1+(1311535459/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668484723/1250000000 : ℝ)*X 1 0+(-1037011807/5000000000 : ℝ)*X 1 1+(2623070819/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((20890147/39062500 : ℝ)*X 2 0+(262307081/500000000 : ℝ)*X 2 1+(-2074023841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155197833/5000000000 : ℝ)*X 0 0+(1034575719/2500000000 : ℝ)*X 0 1+(22444867/50000000 : ℝ)*X 0 2+(2155197833/5000000000 : ℝ)*X 1 0+(1034575719/2500000000 : ℝ)*X 1 1+(22444867/50000000 : ℝ)*X 1 2+(2155197833/5000000000 : ℝ)*X 2 0+(1034575719/2500000000 : ℝ)*X 2 1+(22444867/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1990756723/10000000000 : ℝ)*X 0 0+(2623365959/5000000000 : ℝ)*X 0 1+(270454151/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165795781/312500000 : ℝ)*X 1 0+(-23888533/125000000 : ℝ)*X 1 1+(270454151/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530546499/1000000000 : ℝ)*X 2 0+(2704541511/5000000000 : ℝ)*X 2 1+(-23888533/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862084277/2000000000 : ℝ)*X 0 0+(2243853953/5000000000 : ℝ)*X 0 1+(1034893539/2500000000 : ℝ)*X 0 2+(862084277/2000000000 : ℝ)*X 1 0+(2243853953/5000000000 : ℝ)*X 1 1+(1034893539/2500000000 : ℝ)*X 1 2+(862084277/2000000000 : ℝ)*X 2 0+(2243853953/5000000000 : ℝ)*X 2 1+(1034893539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (282873975026296872414419811/88000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87402393/50000000000000 : ℝ)*(base19) + (36229377/50000000000000 : ℝ)*(lower2) + (59092829/100000000000000 : ℝ)*(lower3) + (8990267/12500000000000 : ℝ)*(lower4) + (90585639/25000000000000 : ℝ)*(lower5) + (4483300175533609/100000000000000 : ℝ)*(major0) + (4483300175533609/100000000000000 : ℝ)*(major1) + (448330017553361/10000000000000 : ℝ)*(major2) + (3057461411768097/50000000000000 : ℝ)*(sp0) + (611492394472363/10000000000000 : ℝ)*(sp1) + (6114924119528417/100000000000000 : ℝ)*(sp2) + (2851676063316353/100000000000000 : ℝ)*(sp3) + (1295992223/100000000000000 : ℝ)*(sp4) + (6107321/10000000000000 : ℝ)*(sp7) + (2851676124389563/100000000000000 : ℝ)*(f.failure) + (6114924119528417/100000000000000 : ℝ)*(f.sum) + (4176816036233/7040000000000000000000000000 : ℝ)*base66 + (969705003209217633/176000000000000000000000000000000 : ℝ)*base68 + (95598256555589243/17600000000000000000000000000000 : ℝ)*base69 + (486028017769217633/176000000000000000000000000000000 : ℝ)*base72 + (24060225906953/7040000000000000000000000000 : ℝ)*base74 + (175492747345989243/17600000000000000000000000000000 : ℝ)*base75 + (103350684292223397/16000000000000000000000000000000 : ℝ)*base77 + (36840588283776603/16000000000000000000000000000000 : ℝ)*base80 + (2526926688277/3520000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (68099471/10000000000000000000000 : ℝ)*base89 + (68099471/10000000000000000000000 : ℝ)*base91 + (31900529/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (660595181512362845748107337/88000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (642519559/50000000000000 : ℝ)*(base19) + (347578119/25000000000000 : ℝ)*(base23) + (15402151/10000000000000 : ℝ)*(upper3) + (24355099/50000000000000 : ℝ)*(lower4) + (153845037/100000000000000 : ℝ)*(upper5) + (4515974056655067/100000000000000 : ℝ)*(major0) + (4515974056655067/100000000000000 : ℝ)*(major1) + (4515974056655067/100000000000000 : ℝ)*(major2) + (26753748889/100000000000000 : ℝ)*(sp1) + (28728281079/100000000000000 : ℝ)*(sp2) + (6159488984242567/100000000000000 : ℝ)*(sp4) + (38496630909091/625000000000 : ℝ)*(sp5) + (1539864716412253/25000000000000 : ℝ)*(sp6) + (718114719710529/25000000000000 : ℝ)*(sp7) + (718114719710529/25000000000000 : ℝ)*(f.failure) + (6159488984242567/100000000000000 : ℝ)*(f.sum) + (10362134299551/3520000000000000000000000000 : ℝ)*base65 + (39409093262108111/16000000000000000000000000000000 : ℝ)*base67 + (2103608081891889/16000000000000000000000000000000 : ℝ)*base70 + (124281516398108111/16000000000000000000000000000000 : ℝ)*base71 + (8064513521569/3520000000000000000000000000 : ℝ)*base74 + (171723607246108111/16000000000000000000000000000000 : ℝ)*base75 + (73362007406108111/16000000000000000000000000000000 : ℝ)*base77 + (25991366545891889/16000000000000000000000000000000 : ℝ)*base80 + (6457133391391/3520000000000000000000000000 : ℝ)*base81 + (501693/2500000000000000000000 : ℝ)*base89 + (501693/2500000000000000000000 : ℝ)*base91 + (501693/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1405_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1405_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1405_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3969/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1405_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1405_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1405_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3969/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1405_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
