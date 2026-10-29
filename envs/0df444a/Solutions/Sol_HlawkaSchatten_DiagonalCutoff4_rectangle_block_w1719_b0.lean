-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1719_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:55:27.153662+00:00
-- url     : https://prove2.me/submissions/2e56d8df-ab2c-40b1-afa5-d7f4f9b5ae63

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
theorem support_rectangle_w1719_s0_0 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1310510161/10000000000 : ℝ)*x 0 + (5680208937/10000000000 : ℝ)*x 1 + (4969489767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310510161/10000000000 : ℝ)^5375 ≤ (812328295833/10000000000000 : ℝ)^4351 := by
    have hnat : (1310510161 : ℕ)^5375*10000000000000^4351 ≤ 812328295833^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310510161 10000000000 812328295833 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5680208937/10000000000 : ℝ)^5375 ≤ (49722664647507/100000000000000 : ℝ)^4351 := by
    have hnat : (5680208937 : ℕ)^5375*100000000000000^4351 ≤ 49722664647507^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680208937 10000000000 49722664647507 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4969489767/10000000000 : ℝ)^5375 ≤ (42154052380817/100000000000000 : ℝ)^4351 := by
    have hnat : (4969489767 : ℕ)^5375*100000000000000^4351 ≤ 42154052380817^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4969489767 10000000000 42154052380817 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1310510161/10000000000 : ℝ), (5680208937/10000000000 : ℝ), (4969489767/10000000000 : ℝ)] ![(812328295833/10000000000000 : ℝ), (49722664647507/100000000000000 : ℝ), (42154052380817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1310510161/10000000000 : ℝ)|^5375 ≤ (812328295833/10000000000000 : ℝ)^4351
        have hw : |(-1310510161/10000000000 : ℝ)|=(1310510161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5680208937/10000000000 : ℝ)|^5375 ≤ (49722664647507/100000000000000 : ℝ)^4351
        have hw : |(5680208937/10000000000 : ℝ)|=(5680208937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4969489767/10000000000 : ℝ)|^5375 ≤ (42154052380817/100000000000000 : ℝ)^4351
        have hw : |(4969489767/10000000000 : ℝ)|=(4969489767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s0_1 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5398059401/10000000000 : ℝ)*x 0 + (-1694259549/10000000000 : ℝ)*x 1 + (4969489187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398059401/10000000000 : ℝ)^5375 ≤ (373516905131/800000000000 : ℝ)^4351 := by
    have hnat : (5398059401 : ℕ)^5375*800000000000^4351 ≤ 373516905131^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398059401 10000000000 373516905131 800000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1694259549/10000000000 : ℝ)^5375 ≤ (557817027143/5000000000000 : ℝ)^4351 := by
    have hnat : (1694259549 : ℕ)^5375*5000000000000^4351 ≤ 557817027143^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694259549 10000000000 557817027143 5000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4969489187/10000000000 : ℝ)^5375 ≤ (21077023151519/50000000000000 : ℝ)^4351 := by
    have hnat : (4969489187 : ℕ)^5375*50000000000000^4351 ≤ 21077023151519^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4969489187 10000000000 21077023151519 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398059401/10000000000 : ℝ), (-1694259549/10000000000 : ℝ), (4969489187/10000000000 : ℝ)] ![(373516905131/800000000000 : ℝ), (557817027143/5000000000000 : ℝ), (21077023151519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398059401/10000000000 : ℝ)|^5375 ≤ (373516905131/800000000000 : ℝ)^4351
        have hw : |(5398059401/10000000000 : ℝ)|=(5398059401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1694259549/10000000000 : ℝ)|^5375 ≤ (557817027143/5000000000000 : ℝ)^4351
        have hw : |(-1694259549/10000000000 : ℝ)|=(1694259549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4969489187/10000000000 : ℝ)|^5375 ≤ (21077023151519/50000000000000 : ℝ)^4351
        have hw : |(4969489187/10000000000 : ℝ)|=(4969489187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s0_2 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699029201/5000000000 : ℝ)*x 0 + (1242372437/2500000000 : ℝ)*x 1 + (-1694260139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699029201/5000000000 : ℝ)^5375 ≤ (23344801233561/50000000000000 : ℝ)^4351 := by
    have hnat : (2699029201 : ℕ)^5375*50000000000000^4351 ≤ 23344801233561^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699029201 5000000000 23344801233561 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1242372437/2500000000 : ℝ)^5375 ≤ (42154052181717/100000000000000 : ℝ)^4351 := by
    have hnat : (1242372437 : ℕ)^5375*100000000000000^4351 ≤ 42154052181717^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242372437 2500000000 42154052181717 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1694260139/10000000000 : ℝ)^5375 ≤ (11156345342219/100000000000000 : ℝ)^4351 := by
    have hnat : (1694260139 : ℕ)^5375*100000000000000^4351 ≤ 11156345342219^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694260139 10000000000 11156345342219 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699029201/5000000000 : ℝ), (1242372437/2500000000 : ℝ), (-1694260139/10000000000 : ℝ)] ![(23344801233561/50000000000000 : ℝ), (42154052181717/100000000000000 : ℝ), (11156345342219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699029201/5000000000 : ℝ)|^5375 ≤ (23344801233561/50000000000000 : ℝ)^4351
        have hw : |(2699029201/5000000000 : ℝ)|=(2699029201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1242372437/2500000000 : ℝ)|^5375 ≤ (42154052181717/100000000000000 : ℝ)^4351
        have hw : |(1242372437/2500000000 : ℝ)|=(1242372437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1694260139/10000000000 : ℝ)|^5375 ≤ (11156345342219/100000000000000 : ℝ)^4351
        have hw : |(-1694260139/10000000000 : ℝ)|=(1694260139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s0_3 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (504010187/1250000000 : ℝ)*x 0 + (766158351/2500000000 : ℝ)*x 1 + (2583763757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504010187/1250000000 : ℝ)^5375 ≤ (3256052016211/10000000000000 : ℝ)^4351 := by
    have hnat : (504010187 : ℕ)^5375*10000000000000^4351 ≤ 3256052016211^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504010187 1250000000 3256052016211 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (766158351/2500000000 : ℝ)^5375 ≤ (2900071183389/12500000000000 : ℝ)^4351 := by
    have hnat : (766158351 : ℕ)^5375*12500000000000^4351 ≤ 2900071183389^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766158351 2500000000 2900071183389 12500000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583763757/5000000000 : ℝ)^5375 ≤ (44238910357921/100000000000000 : ℝ)^4351 := by
    have hnat : (2583763757 : ℕ)^5375*100000000000000^4351 ≤ 44238910357921^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583763757 5000000000 44238910357921 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(504010187/1250000000 : ℝ), (766158351/2500000000 : ℝ), (2583763757/5000000000 : ℝ)] ![(3256052016211/10000000000000 : ℝ), (2900071183389/12500000000000 : ℝ), (44238910357921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(504010187/1250000000 : ℝ)|^5375 ≤ (3256052016211/10000000000000 : ℝ)^4351
        have hw : |(504010187/1250000000 : ℝ)|=(504010187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(766158351/2500000000 : ℝ)|^5375 ≤ (2900071183389/12500000000000 : ℝ)^4351
        have hw : |(766158351/2500000000 : ℝ)|=(766158351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583763757/5000000000 : ℝ)|^5375 ≤ (44238910357921/100000000000000 : ℝ)^4351
        have hw : |(2583763757/5000000000 : ℝ)|=(2583763757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s0_4 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-656022159/5000000000 : ℝ)*x 0 + (4986782841/10000000000 : ℝ)*x 1 + (5662351451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656022159/5000000000 : ℝ)^5375 ≤ (496522962/6103515625 : ℝ)^4351 := by
    have hnat : (656022159 : ℕ)^5375*6103515625^4351 ≤ 496522962^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656022159 5000000000 496522962 6103515625 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4986782841/10000000000 : ℝ)^5375 ≤ (42335339421643/100000000000000 : ℝ)^4351 := by
    have hnat : (4986782841 : ℕ)^5375*100000000000000^4351 ≤ 42335339421643^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986782841 10000000000 42335339421643 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5662351451/10000000000 : ℝ)^5375 ≤ (49529628356853/100000000000000 : ℝ)^4351 := by
    have hnat : (5662351451 : ℕ)^5375*100000000000000^4351 ≤ 49529628356853^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662351451 10000000000 49529628356853 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-656022159/5000000000 : ℝ), (4986782841/10000000000 : ℝ), (5662351451/10000000000 : ℝ)] ![(496522962/6103515625 : ℝ), (42335339421643/100000000000000 : ℝ), (49529628356853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-656022159/5000000000 : ℝ)|^5375 ≤ (496522962/6103515625 : ℝ)^4351
        have hw : |(-656022159/5000000000 : ℝ)|=(656022159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4986782841/10000000000 : ℝ)|^5375 ≤ (42335339421643/100000000000000 : ℝ)^4351
        have hw : |(4986782841/10000000000 : ℝ)|=(4986782841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5662351451/10000000000 : ℝ)|^5375 ≤ (49529628356853/100000000000000 : ℝ)^4351
        have hw : |(5662351451/10000000000 : ℝ)|=(5662351451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s0_5 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301448233/2500000000 : ℝ)*x 0 + (-50069943/500000000 : ℝ)*x 1 + (2831175917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301448233/2500000000 : ℝ)^5375 ≤ (5580493458199/12500000000000 : ℝ)^4351 := by
    have hnat : (1301448233 : ℕ)^5375*12500000000000^4351 ≤ 5580493458199^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301448233 2500000000 5580493458199 12500000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50069943/500000000 : ℝ)^5375 ≤ (1165283965867/20000000000000 : ℝ)^4351 := by
    have hnat : (50069943 : ℕ)^5375*20000000000000^4351 ≤ 1165283965867^4351*500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50069943 500000000 1165283965867 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831175917/5000000000 : ℝ)^5375 ≤ (49529632495481/100000000000000 : ℝ)^4351 := by
    have hnat : (2831175917 : ℕ)^5375*100000000000000^4351 ≤ 49529632495481^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831175917 5000000000 49529632495481 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301448233/2500000000 : ℝ), (-50069943/500000000 : ℝ), (2831175917/5000000000 : ℝ)] ![(5580493458199/12500000000000 : ℝ), (1165283965867/20000000000000 : ℝ), (49529632495481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301448233/2500000000 : ℝ)|^5375 ≤ (5580493458199/12500000000000 : ℝ)^4351
        have hw : |(1301448233/2500000000 : ℝ)|=(1301448233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50069943/500000000 : ℝ)|^5375 ≤ (1165283965867/20000000000000 : ℝ)^4351
        have hw : |(-50069943/500000000 : ℝ)|=(50069943/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2831175917/5000000000 : ℝ)|^5375 ≤ (49529632495481/100000000000000 : ℝ)^4351
        have hw : |(2831175917/5000000000 : ℝ)|=(2831175917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s0_6 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2602897023/5000000000 : ℝ)*x 0 + (5662350917/10000000000 : ℝ)*x 1 + (-250349649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2602897023/5000000000 : ℝ)^5375 ≤ (5580494933431/12500000000000 : ℝ)^4351 := by
    have hnat : (2602897023 : ℕ)^5375*12500000000000^4351 ≤ 5580494933431^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602897023 5000000000 5580494933431 12500000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5662350917/10000000000 : ℝ)^5375 ≤ (49529622586547/100000000000000 : ℝ)^4351 := by
    have hnat : (5662350917 : ℕ)^5375*100000000000000^4351 ≤ 49529622586547^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662350917 10000000000 49529622586547 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250349649/2500000000 : ℝ)^5375 ≤ (182075560369/3125000000000 : ℝ)^4351 := by
    have hnat : (250349649 : ℕ)^5375*3125000000000^4351 ≤ 182075560369^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250349649 2500000000 182075560369 3125000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2602897023/5000000000 : ℝ), (5662350917/10000000000 : ℝ), (-250349649/2500000000 : ℝ)] ![(5580494933431/12500000000000 : ℝ), (49529622586547/100000000000000 : ℝ), (182075560369/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2602897023/5000000000 : ℝ)|^5375 ≤ (5580494933431/12500000000000 : ℝ)^4351
        have hw : |(2602897023/5000000000 : ℝ)|=(2602897023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5662350917/10000000000 : ℝ)|^5375 ≤ (49529622586547/100000000000000 : ℝ)^4351
        have hw : |(5662350917/10000000000 : ℝ)|=(5662350917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250349649/2500000000 : ℝ)|^5375 ≤ (182075560369/3125000000000 : ℝ)^4351
        have hw : |(-250349649/2500000000 : ℝ)|=(250349649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s0_7 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4036624757/10000000000 : ℝ)*x 0 + (639545139/1250000000 : ℝ)*x 1 + (1558736601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4036624757/10000000000 : ℝ)^5375 ≤ (16302924608741/50000000000000 : ℝ)^4351 := by
    have hnat : (4036624757 : ℕ)^5375*50000000000000^4351 ≤ 16302924608741^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036624757 10000000000 16302924608741 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639545139/1250000000 : ℝ)^5375 ≤ (349587356633/800000000000 : ℝ)^4351 := by
    have hnat : (639545139 : ℕ)^5375*800000000000^4351 ≤ 349587356633^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639545139 1250000000 349587356633 800000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1558736601/5000000000 : ℝ)^5375 ≤ (23695731190397/100000000000000 : ℝ)^4351 := by
    have hnat : (1558736601 : ℕ)^5375*100000000000000^4351 ≤ 23695731190397^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558736601 5000000000 23695731190397 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4036624757/10000000000 : ℝ), (639545139/1250000000 : ℝ), (1558736601/5000000000 : ℝ)] ![(16302924608741/50000000000000 : ℝ), (349587356633/800000000000 : ℝ), (23695731190397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4036624757/10000000000 : ℝ)|^5375 ≤ (16302924608741/50000000000000 : ℝ)^4351
        have hw : |(4036624757/10000000000 : ℝ)|=(4036624757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(639545139/1250000000 : ℝ)|^5375 ≤ (349587356633/800000000000 : ℝ)^4351
        have hw : |(639545139/1250000000 : ℝ)|=(639545139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1558736601/5000000000 : ℝ)|^5375 ≤ (23695731190397/100000000000000 : ℝ)^4351
        have hw : |(1558736601/5000000000 : ℝ)|=(1558736601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1719_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3153/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21599/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (5367/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5367 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5367*1^1024 ≤ 0^1024*1^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5367/1024 : ℝ) ≤ (82094199814369883/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5367 ≤ (82094199814369883/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5367*10000000000000000000^1024 ≤ 82094199814369883^1024*5^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 82094199814369883 10000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (82094199814369883/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5367 := by
      have hnat : (1 : ℕ)^1024*1^5367 ≤ 1^5367*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10082094199814369883/10000000000000000000 : ℝ) ≤ (10015611442300589/10000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (10082094199814369883/10000000000000000000 : ℝ)^1024 ≤ (10015611442300589/10000000000000000 : ℝ)^5367 := by
      have hnat : (10082094199814369883 : ℕ)^1024*10000000000000000^5367 ≤ 10015611442300589^5367*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10082094199814369883 10000000000000000000 10015611442300589 10000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015611442300589/10000000000000000 : ℝ)) (X := (10082094199814369883/10000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5082094199814369883/5000000000000000000 : ℝ) ≤ (5015611442300589/5000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (5082094199814369883/5000000000000000000 : ℝ)^1024 ≤ (5015611442300589/5000000000000000 : ℝ)^5367 := by
      have hnat : (5082094199814369883 : ℕ)^1024*5000000000000000^5367 ≤ 5015611442300589^5367*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5082094199814369883 5000000000000000000 5015611442300589 5000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015611442300589/5000000000000000 : ℝ)) (X := (5082094199814369883/5000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15611442300589/4000000000000000 : ℝ)*(0 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15611442300589/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(82094199814369883/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15611442300589/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5367/1024 : ℝ) := by
    rw [show (1 : ℝ)+(15611442300589/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10015611442300589/10000000000000000 : ℝ) by norm_num, show 1+(82094199814369883/10000000000000000000 : ℝ)+(0 : ℝ)=(10082094199814369883/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(82094199814369883/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15611442300589/4000000000000000 : ℝ)*(2/5 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15611442300589/4000000000000000 : ℝ)*(2/5 : ℝ)=(5015611442300589/5000000000000000 : ℝ) by norm_num, show 1+2*(82094199814369883/10000000000000000000 : ℝ)=(5082094199814369883/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15611442300589/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15611442300589/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15611442300589/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15611442300589/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15611442300589/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15611442300589/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1310510161/10000000000 : ℝ)*X 0 0+(5680208937/10000000000 : ℝ)*X 0 1+(4969489767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5398059401/10000000000 : ℝ)*X 1 0+(-1694259549/10000000000 : ℝ)*X 1 1+(4969489187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2699029201/5000000000 : ℝ)*X 2 0+(1242372437/2500000000 : ℝ)*X 2 1+(-1694260139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((504010187/1250000000 : ℝ)*X 0 0+(766158351/2500000000 : ℝ)*X 0 1+(2583763757/5000000000 : ℝ)*X 0 2+(504010187/1250000000 : ℝ)*X 1 0+(766158351/2500000000 : ℝ)*X 1 1+(2583763757/5000000000 : ℝ)*X 1 2+(504010187/1250000000 : ℝ)*X 2 0+(766158351/2500000000 : ℝ)*X 2 1+(2583763757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-656022159/5000000000 : ℝ)*X 0 0+(4986782841/10000000000 : ℝ)*X 0 1+(5662351451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1301448233/2500000000 : ℝ)*X 1 0+(-50069943/500000000 : ℝ)*X 1 1+(2831175917/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2602897023/5000000000 : ℝ)*X 2 0+(5662350917/10000000000 : ℝ)*X 2 1+(-250349649/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4036624757/10000000000 : ℝ)*X 0 0+(639545139/1250000000 : ℝ)*X 0 1+(1558736601/5000000000 : ℝ)*X 0 2+(4036624757/10000000000 : ℝ)*X 1 0+(639545139/1250000000 : ℝ)*X 1 1+(1558736601/5000000000 : ℝ)*X 1 2+(4036624757/10000000000 : ℝ)*X 2 0+(639545139/1250000000 : ℝ)*X 2 1+(1558736601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (405159724311345202796721/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35771933/25000000000000 : ℝ)*(base1) + (8811723/100000000000000 : ℝ)*(base16) + (66985091/12500000000000 : ℝ)*(base19) + (25506543/10000000000000 : ℝ)*(base23) + (112481539/100000000000000 : ℝ)*(upper3) + (941281218034579/100000000000000 : ℝ)*(major0) + (941281218034579/100000000000000 : ℝ)*(major1) + (941281218034579/100000000000000 : ℝ)*(major2) + (703513536844811/50000000000000 : ℝ)*(sp0) + (4396957455967/312500000000 : ℝ)*(sp1) + (1407025854769599/100000000000000 : ℝ)*(sp2) + (475535092159393/100000000000000 : ℝ)*(sp3) + (820766861/100000000000000 : ℝ)*(sp6) + (202693519/100000000000000 : ℝ)*(sp7) + (118883859485161/25000000000000 : ℝ)*(f.failure) + (140702693060189/10000000000000 : ℝ)*(f.sum) + (27002180267031/200000000000000000000000000000 : ℝ)*base65 + (966201228467031/400000000000000000000000000000 : ℝ)*base67 + (1297814748467031/400000000000000000000000000000 : ℝ)*base69 + (322745813667031/400000000000000000000000000000 : ℝ)*base71 + (8709846067031/200000000000000000000000000000 : ℝ)*base73 + (2613436133932969/400000000000000000000000000000 : ℝ)*base76 + (1411791828067031/400000000000000000000000000000 : ℝ)*base77 + (1481968918467031/400000000000000000000000000000 : ℝ)*base79 + (203734370532969/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (172787/125000000000000000000 : ℝ)*base89 + (172787/125000000000000000000 : ℝ)*base91 + (172787/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117552330111830608122159/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79166163/50000000000000 : ℝ)*(base1) + (94021089/12500000000000 : ℝ)*(base19) + (567111521/50000000000000 : ℝ)*(base23) + (145950121/25000000000000 : ℝ)*(base32) + (229453057/100000000000000 : ℝ)*(upper3) + (247563710118377/25000000000000 : ℝ)*(major0) + (247563710118377/25000000000000 : ℝ)*(major1) + (247563710118377/25000000000000 : ℝ)*(major2) + (921551191/100000000000000 : ℝ)*(sp1) + (1344767003/50000000000000 : ℝ)*(sp2) + (296046505354801/20000000000000 : ℝ)*(sp4) + (92514418420111/6250000000000 : ℝ)*(sp5) + (185028568085579/12500000000000 : ℝ)*(sp6) + (250138089265709/50000000000000 : ℝ)*(sp7) + (500276920664227/100000000000000 : ℝ)*(f.failure) + (18502904605521/1250000000000 : ℝ)*(f.sum) + (99807684975947/50000000000000000000000000000 : ℝ)*base66 + (170696095275947/100000000000000000000000000000 : ℝ)*base68 + (905358762275947/100000000000000000000000000000 : ℝ)*base70 + (725139518075947/100000000000000000000000000000 : ℝ)*base72 + (45158023025947/50000000000000000000000000000 : ℝ)*base74 + (311243473124053/100000000000000000000000000000 : ℝ)*base75 + (673013084175947/100000000000000000000000000000 : ℝ)*base78 + (1168349077975947/100000000000000000000000000000 : ℝ)*base80 + (252854439675947/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (877791/500000000000000000000 : ℝ)*base90 + (877791/500000000000000000000 : ℝ)*base92 + (877791/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1719_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3153/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21599/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1719_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1719_s1_0 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86077089/625000000 : ℝ)*x 0 + (1369153459/2500000000 : ℝ)*x 1 + (102581067/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86077089/625000000 : ℝ)^5375 ≤ (2159307752169/25000000000000 : ℝ)^4351 := by
    have hnat : (86077089 : ℕ)^5375*25000000000000^4351 ≤ 2159307752169^4351*625000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86077089 625000000 2159307752169 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369153459/2500000000 : ℝ)^5375 ≤ (11882598608123/25000000000000 : ℝ)^4351 := by
    have hnat : (1369153459 : ℕ)^5375*25000000000000^4351 ≤ 11882598608123^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369153459 2500000000 11882598608123 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102581067/200000000 : ℝ)^5375 ≤ (43832374543273/100000000000000 : ℝ)^4351 := by
    have hnat : (102581067 : ℕ)^5375*100000000000000^4351 ≤ 43832374543273^4351*200000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102581067 200000000 43832374543273 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86077089/625000000 : ℝ), (1369153459/2500000000 : ℝ), (102581067/200000000 : ℝ)] ![(2159307752169/25000000000000 : ℝ), (11882598608123/25000000000000 : ℝ), (43832374543273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86077089/625000000 : ℝ)|^5375 ≤ (2159307752169/25000000000000 : ℝ)^4351
        have hw : |(-86077089/625000000 : ℝ)|=(86077089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369153459/2500000000 : ℝ)|^5375 ≤ (11882598608123/25000000000000 : ℝ)^4351
        have hw : |(1369153459/2500000000 : ℝ)|=(1369153459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102581067/200000000 : ℝ)|^5375 ≤ (43832374543273/100000000000000 : ℝ)^4351
        have hw : |(102581067/200000000 : ℝ)|=(102581067/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s1_1 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068766771/2000000000 : ℝ)*x 0 + (-1557759717/10000000000 : ℝ)*x 1 + (102581047/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068766771/2000000000 : ℝ)^5375 ≤ (4611090320599/10000000000000 : ℝ)^4351 := by
    have hnat : (1068766771 : ℕ)^5375*10000000000000^4351 ≤ 4611090320599^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068766771 2000000000 4611090320599 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557759717/10000000000 : ℝ)^5375 ≤ (5028366398077/50000000000000 : ℝ)^4351 := by
    have hnat : (1557759717 : ℕ)^5375*50000000000000^4351 ≤ 5028366398077^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557759717 10000000000 5028366398077 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102581047/200000000 : ℝ)^5375 ≤ (684880687283/1562500000000 : ℝ)^4351 := by
    have hnat : (102581047 : ℕ)^5375*1562500000000^4351 ≤ 684880687283^4351*200000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102581047 200000000 684880687283 1562500000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068766771/2000000000 : ℝ), (-1557759717/10000000000 : ℝ), (102581047/200000000 : ℝ)] ![(4611090320599/10000000000000 : ℝ), (5028366398077/50000000000000 : ℝ), (684880687283/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068766771/2000000000 : ℝ)|^5375 ≤ (4611090320599/10000000000000 : ℝ)^4351
        have hw : |(1068766771/2000000000 : ℝ)|=(1068766771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1557759717/10000000000 : ℝ)|^5375 ≤ (5028366398077/50000000000000 : ℝ)^4351
        have hw : |(-1557759717/10000000000 : ℝ)|=(1557759717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102581047/200000000 : ℝ)|^5375 ≤ (684880687283/1562500000000 : ℝ)^4351
        have hw : |(102581047/200000000 : ℝ)|=(102581047/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s1_2 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343832641/10000000000 : ℝ)*x 0 + (2564526631/5000000000 : ℝ)*x 1 + (-1557760133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343832641/10000000000 : ℝ)^5375 ≤ (46110890265261/100000000000000 : ℝ)^4351 := by
    have hnat : (5343832641 : ℕ)^5375*100000000000000^4351 ≤ 46110890265261^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343832641 10000000000 46110890265261 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564526631/5000000000 : ℝ)^5375 ≤ (43832373614243/100000000000000 : ℝ)^4351 := by
    have hnat : (2564526631 : ℕ)^5375*100000000000000^4351 ≤ 43832373614243^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564526631 5000000000 43832373614243 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557760133/10000000000 : ℝ)^5375 ≤ (1005673611387/10000000000000 : ℝ)^4351 := by
    have hnat : (1557760133 : ℕ)^5375*10000000000000^4351 ≤ 1005673611387^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557760133 10000000000 1005673611387 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343832641/10000000000 : ℝ), (2564526631/5000000000 : ℝ), (-1557760133/10000000000 : ℝ)] ![(46110890265261/100000000000000 : ℝ), (43832373614243/100000000000000 : ℝ), (1005673611387/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343832641/10000000000 : ℝ)|^5375 ≤ (46110890265261/100000000000000 : ℝ)^4351
        have hw : |(5343832641/10000000000 : ℝ)|=(5343832641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564526631/5000000000 : ℝ)|^5375 ≤ (43832373614243/100000000000000 : ℝ)^4351
        have hw : |(2564526631/5000000000 : ℝ)|=(2564526631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1557760133/10000000000 : ℝ)|^5375 ≤ (1005673611387/10000000000000 : ℝ)^4351
        have hw : |(-1557760133/10000000000 : ℝ)|=(1557760133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s1_3 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6545621/16000000 : ℝ)*x 0 + (179839353/500000000 : ℝ)*x 1 + (4625154467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6545621/16000000 : ℝ)^5375 ≤ (33149422665117/100000000000000 : ℝ)^4351 := by
    have hnat : (6545621 : ℕ)^5375*100000000000000^4351 ≤ 33149422665117^4351*16000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6545621 16000000 33149422665117 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179839353/500000000 : ℝ)^5375 ≤ (7068708426193/25000000000000 : ℝ)^4351 := by
    have hnat : (179839353 : ℕ)^5375*25000000000000^4351 ≤ 7068708426193^4351*500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179839353 500000000 7068708426193 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4625154467/10000000000 : ℝ)^5375 ≤ (4821967952203/12500000000000 : ℝ)^4351 := by
    have hnat : (4625154467 : ℕ)^5375*12500000000000^4351 ≤ 4821967952203^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4625154467 10000000000 4821967952203 12500000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6545621/16000000 : ℝ), (179839353/500000000 : ℝ), (4625154467/10000000000 : ℝ)] ![(33149422665117/100000000000000 : ℝ), (7068708426193/25000000000000 : ℝ), (4821967952203/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6545621/16000000 : ℝ)|^5375 ≤ (33149422665117/100000000000000 : ℝ)^4351
        have hw : |(6545621/16000000 : ℝ)|=(6545621/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179839353/500000000 : ℝ)|^5375 ≤ (7068708426193/25000000000000 : ℝ)^4351
        have hw : |(179839353/500000000 : ℝ)|=(179839353/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4625154467/10000000000 : ℝ)|^5375 ≤ (4821967952203/12500000000000 : ℝ)^4351
        have hw : |(4625154467/10000000000 : ℝ)|=(4625154467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s1_4 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1377413269/10000000000 : ℝ)*x 0 + (12832997/25000000 : ℝ)*x 1 + (1368100283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377413269/10000000000 : ℝ)^5375 ≤ (8638624362481/100000000000000 : ℝ)^4351 := by
    have hnat : (1377413269 : ℕ)^5375*100000000000000^4351 ≤ 8638624362481^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377413269 10000000000 8638624362481 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12832997/25000000 : ℝ)^5375 ≤ (10969035722517/25000000000000 : ℝ)^4351 := by
    have hnat : (12832997 : ℕ)^5375*25000000000000^4351 ≤ 10969035722517^4351*25000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12832997 25000000 10969035722517 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368100283/2500000000 : ℝ)^5375 ≤ (47485232729639/100000000000000 : ℝ)^4351 := by
    have hnat : (1368100283 : ℕ)^5375*100000000000000^4351 ≤ 47485232729639^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368100283 2500000000 47485232729639 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1377413269/10000000000 : ℝ), (12832997/25000000 : ℝ), (1368100283/2500000000 : ℝ)] ![(8638624362481/100000000000000 : ℝ), (10969035722517/25000000000000 : ℝ), (47485232729639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1377413269/10000000000 : ℝ)|^5375 ≤ (8638624362481/100000000000000 : ℝ)^4351
        have hw : |(-1377413269/10000000000 : ℝ)|=(1377413269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12832997/25000000 : ℝ)|^5375 ≤ (10969035722517/25000000000000 : ℝ)^4351
        have hw : |(12832997/25000000 : ℝ)|=(12832997/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368100283/2500000000 : ℝ)|^5375 ≤ (47485232729639/100000000000000 : ℝ)^4351
        have hw : |(1368100283/2500000000 : ℝ)|=(1368100283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s1_5 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050153187/2000000000 : ℝ)*x 0 + (-1214411579/10000000000 : ℝ)*x 1 + (684050087/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050153187/2000000000 : ℝ)^5375 ≤ (9024176113039/20000000000000 : ℝ)^4351 := by
    have hnat : (1050153187 : ℕ)^5375*20000000000000^4351 ≤ 9024176113039^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050153187 2000000000 9024176113039 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214411579/10000000000 : ℝ)^5375 ≤ (7393891372209/100000000000000 : ℝ)^4351 := by
    have hnat : (1214411579 : ℕ)^5375*100000000000000^4351 ≤ 7393891372209^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214411579 10000000000 7393891372209 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684050087/1250000000 : ℝ)^5375 ≤ (9497045611197/20000000000000 : ℝ)^4351 := by
    have hnat : (684050087 : ℕ)^5375*20000000000000^4351 ≤ 9497045611197^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684050087 1250000000 9497045611197 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050153187/2000000000 : ℝ), (-1214411579/10000000000 : ℝ), (684050087/1250000000 : ℝ)] ![(9024176113039/20000000000000 : ℝ), (7393891372209/100000000000000 : ℝ), (9497045611197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050153187/2000000000 : ℝ)|^5375 ≤ (9024176113039/20000000000000 : ℝ)^4351
        have hw : |(1050153187/2000000000 : ℝ)|=(1050153187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1214411579/10000000000 : ℝ)|^5375 ≤ (7393891372209/100000000000000 : ℝ)^4351
        have hw : |(-1214411579/10000000000 : ℝ)|=(1214411579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684050087/1250000000 : ℝ)|^5375 ≤ (9497045611197/20000000000000 : ℝ)^4351
        have hw : |(684050087/1250000000 : ℝ)|=(684050087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s1_6 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625383089/5000000000 : ℝ)*x 0 + (218896017/400000000 : ℝ)*x 1 + (-1214411621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625383089/5000000000 : ℝ)^5375 ≤ (9024176628957/20000000000000 : ℝ)^4351 := by
    have hnat : (2625383089 : ℕ)^5375*20000000000000^4351 ≤ 9024176628957^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625383089 5000000000 9024176628957 20000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218896017/400000000 : ℝ)^5375 ≤ (47485225151031/100000000000000 : ℝ)^4351 := by
    have hnat : (218896017 : ℕ)^5375*100000000000000^4351 ≤ 47485225151031^4351*400000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218896017 400000000 47485225151031 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1214411621/10000000000 : ℝ)^5375 ≤ (3696945844053/50000000000000 : ℝ)^4351 := by
    have hnat : (1214411621 : ℕ)^5375*50000000000000^4351 ≤ 3696945844053^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214411621 10000000000 3696945844053 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625383089/5000000000 : ℝ), (218896017/400000000 : ℝ), (-1214411621/10000000000 : ℝ)] ![(9024176628957/20000000000000 : ℝ), (47485225151031/100000000000000 : ℝ), (3696945844053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625383089/5000000000 : ℝ)|^5375 ≤ (9024176628957/20000000000000 : ℝ)^4351
        have hw : |(2625383089/5000000000 : ℝ)|=(2625383089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218896017/400000000 : ℝ)|^5375 ≤ (47485225151031/100000000000000 : ℝ)^4351
        have hw : |(218896017/400000000 : ℝ)|=(218896017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1214411621/10000000000 : ℝ)|^5375 ≤ (3696945844053/50000000000000 : ℝ)^4351
        have hw : |(-1214411621/10000000000 : ℝ)|=(1214411621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s1_7 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4091540557/10000000000 : ℝ)*x 0 + (922577663/2000000000 : ℝ)*x 1 + (3609248261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4091540557/10000000000 : ℝ)^5375 ≤ (8288675586111/25000000000000 : ℝ)^4351 := by
    have hnat : (4091540557 : ℕ)^5375*25000000000000^4351 ≤ 8288675586111^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4091540557 10000000000 8288675586111 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922577663/2000000000 : ℝ)^5375 ≤ (38449400919903/100000000000000 : ℝ)^4351 := by
    have hnat : (922577663 : ℕ)^5375*100000000000000^4351 ≤ 38449400919903^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922577663 2000000000 38449400919903 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3609248261/10000000000 : ℝ)^5375 ≤ (28395896718939/100000000000000 : ℝ)^4351 := by
    have hnat : (3609248261 : ℕ)^5375*100000000000000^4351 ≤ 28395896718939^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3609248261 10000000000 28395896718939 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4091540557/10000000000 : ℝ), (922577663/2000000000 : ℝ), (3609248261/10000000000 : ℝ)] ![(8288675586111/25000000000000 : ℝ), (38449400919903/100000000000000 : ℝ), (28395896718939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4091540557/10000000000 : ℝ)|^5375 ≤ (8288675586111/25000000000000 : ℝ)^4351
        have hw : |(4091540557/10000000000 : ℝ)|=(4091540557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922577663/2000000000 : ℝ)|^5375 ≤ (38449400919903/100000000000000 : ℝ)^4351
        have hw : |(922577663/2000000000 : ℝ)|=(922577663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3609248261/10000000000 : ℝ)|^5375 ≤ (28395896718939/100000000000000 : ℝ)^4351
        have hw : |(3609248261/10000000000 : ℝ)|=(3609248261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1719_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21599/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3153/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1971/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17287/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21599/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3153/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21599/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3153/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21599/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3153/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21599/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3153/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21599/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3153/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21599/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3153/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3153/50000 : ℝ) ^ (5367/1024 : ℝ) ≤ (51198514588599/100000000000000000000 : ℝ) := by
    have hpowers : (3153/50000 : ℝ)^5367 ≤ (51198514588599/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3153 : ℕ)^5367*100000000000000000000^1024 ≤ 51198514588599^1024*50000^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3153 50000 51198514588599 100000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3153/50000 : ℝ)) (X := (51198514588599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21599/100000 : ℝ) ^ (5367/1024 : ℝ) ≤ (6496154321409819/20000000000000000000 : ℝ) := by
    have hpowers : (21599/100000 : ℝ)^5367 ≤ (6496154321409819/20000000000000000000 : ℝ)^1024 := by
      have hnat : (21599 : ℕ)^5367*20000000000000000000^1024 ≤ 6496154321409819^1024*100000^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21599 100000 6496154321409819 20000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21599/100000 : ℝ)) (X := (6496154321409819/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051198514588599/50000000000000000000 : ℝ) ≤ (10000001953689481/10000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (50000051198514588599/50000000000000000000 : ℝ)^1024 ≤ (10000001953689481/10000000000000000 : ℝ)^5367 := by
      have hnat : (50000051198514588599 : ℕ)^1024*10000000000000000^5367 ≤ 10000001953689481^5367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051198514588599 50000000000000000000 10000001953689481 10000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001953689481/10000000000000000 : ℝ)) (X := (50000051198514588599/50000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016265985060818847/50000000000000000000 : ℝ) ≤ (500031030700087/500000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (50016265985060818847/50000000000000000000 : ℝ)^1024 ≤ (500031030700087/500000000000000 : ℝ)^5367 := by
      have hnat : (50016265985060818847 : ℕ)^1024*500000000000000^5367 ≤ 500031030700087^5367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016265985060818847 50000000000000000000 500031030700087 500000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500031030700087/500000000000000 : ℝ)) (X := (50016265985060818847/50000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006496154321409819/10000000000000000000 : ℝ) ≤ (10001239274313999/10000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (10006496154321409819/10000000000000000000 : ℝ)^1024 ≤ (10001239274313999/10000000000000000 : ℝ)^5367 := by
      have hnat : (10006496154321409819 : ℕ)^1024*10000000000000000^5367 ≤ 10001239274313999^5367*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006496154321409819 10000000000000000000 10001239274313999 10000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001239274313999/10000000000000000 : ℝ)) (X := (10006496154321409819/10000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51198514588599/100000000000000000000 : ℝ) ≤ ((6116889093356600897/6117200000000000000 : ℝ)+2*(618660312259/1529300000000000 : ℝ)*(3153/50000 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (6116889093356600897/6117200000000000000 : ℝ)+2*(618660312259/1529300000000000 : ℝ)*(3153/50000 : ℝ)=(10000001953689481/10000000000000000 : ℝ) by norm_num, show 1+2*(51198514588599/100000000000000000000 : ℝ)=(50000051198514588599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6496154321409819/20000000000000000000 : ℝ)+(51198514588599/100000000000000000000 : ℝ) ≤ ((6116889093356600897/6117200000000000000 : ℝ)+(618660312259/1529300000000000 : ℝ)*((21599/100000 : ℝ)+(3153/50000 : ℝ)))^(5367/1024 : ℝ) := by
    rw [show (6116889093356600897/6117200000000000000 : ℝ)+(618660312259/1529300000000000 : ℝ)*((21599/100000 : ℝ)+(3153/50000 : ℝ))=(500031030700087/500000000000000 : ℝ) by norm_num, show 1+(6496154321409819/20000000000000000000 : ℝ)+(51198514588599/100000000000000000000 : ℝ)=(50016265985060818847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6496154321409819/20000000000000000000 : ℝ) ≤ ((6116889093356600897/6117200000000000000 : ℝ)+2*(618660312259/1529300000000000 : ℝ)*(21599/100000 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (6116889093356600897/6117200000000000000 : ℝ)+2*(618660312259/1529300000000000 : ℝ)*(21599/100000 : ℝ)=(10001239274313999/10000000000000000 : ℝ) by norm_num, show 1+2*(6496154321409819/20000000000000000000 : ℝ)=(10006496154321409819/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6116889093356600897/6117200000000000000 : ℝ)*(X 1 0+X 2 0)+(618660312259/1529300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (3153/50000 : ℝ)) (hi := (21599/100000 : ℝ)) (c := (6116889093356600897/6117200000000000000 : ℝ)) (alpha := (618660312259/1529300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6116889093356600897/6117200000000000000 : ℝ)*(X 0 1+X 2 1)+(618660312259/1529300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (3153/50000 : ℝ)) (hi := (21599/100000 : ℝ)) (c := (6116889093356600897/6117200000000000000 : ℝ)) (alpha := (618660312259/1529300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6116889093356600897/6117200000000000000 : ℝ)*(X 0 2+X 1 2)+(618660312259/1529300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (3153/50000 : ℝ)) (hi := (21599/100000 : ℝ)) (c := (6116889093356600897/6117200000000000000 : ℝ)) (alpha := (618660312259/1529300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-86077089/625000000 : ℝ)*X 0 0+(1369153459/2500000000 : ℝ)*X 0 1+(102581067/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068766771/2000000000 : ℝ)*X 1 0+(-1557759717/10000000000 : ℝ)*X 1 1+(102581047/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5343832641/10000000000 : ℝ)*X 2 0+(2564526631/5000000000 : ℝ)*X 2 1+(-1557760133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((6545621/16000000 : ℝ)*X 0 0+(179839353/500000000 : ℝ)*X 0 1+(4625154467/10000000000 : ℝ)*X 0 2+(6545621/16000000 : ℝ)*X 1 0+(179839353/500000000 : ℝ)*X 1 1+(4625154467/10000000000 : ℝ)*X 1 2+(6545621/16000000 : ℝ)*X 2 0+(179839353/500000000 : ℝ)*X 2 1+(4625154467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1377413269/10000000000 : ℝ)*X 0 0+(12832997/25000000 : ℝ)*X 0 1+(1368100283/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050153187/2000000000 : ℝ)*X 1 0+(-1214411579/10000000000 : ℝ)*X 1 1+(684050087/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625383089/5000000000 : ℝ)*X 2 0+(218896017/400000000 : ℝ)*X 2 1+(-1214411621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4091540557/10000000000 : ℝ)*X 0 0+(922577663/2000000000 : ℝ)*X 0 1+(3609248261/10000000000 : ℝ)*X 0 2+(4091540557/10000000000 : ℝ)*X 1 0+(922577663/2000000000 : ℝ)*X 1 1+(3609248261/10000000000 : ℝ)*X 1 2+(4091540557/10000000000 : ℝ)*X 2 0+(922577663/2000000000 : ℝ)*X 2 1+(3609248261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (906876494311717630926885051/76465000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35921831/3125000000000 : ℝ)*(base19) + (383630491/50000000000000 : ℝ)*(base23) + (50088891/50000000000000 : ℝ)*(lower2) + (35766593/25000000000000 : ℝ)*(upper3) + (4904193/2000000000000 : ℝ)*(lower4) + (962406847723961/50000000000000 : ℝ)*(major0) + (962406847723961/50000000000000 : ℝ)*(major1) + (962406847723961/50000000000000 : ℝ)*(major2) + (89912719222929/3125000000000 : ℝ)*(sp0) + (719302406616519/25000000000000 : ℝ)*(sp1) + (1438605004351843/50000000000000 : ℝ)*(sp2) + (972415833485437/100000000000000 : ℝ)*(sp3) + (3760830941/100000000000000 : ℝ)*(sp4) + (386111703/100000000000000 : ℝ)*(sp7) + (48620810979857/5000000000000 : ℝ)*(f.failure) + (719302693991167/25000000000000 : ℝ)*(f.sum) + (267312575602123/76465000000000000000000000000 : ℝ)*base65 + (1267234955295190983/305860000000000000000000000000000 : ℝ)*base68 + (2062740877051050983/305860000000000000000000000000000 : ℝ)*base70 + (1467466919701229017/305860000000000000000000000000000 : ℝ)*base71 + (91143579172353/76465000000000000000000000000 : ℝ)*base73 + (2741035767936730983/305860000000000000000000000000000 : ℝ)*base76 + (1715315832930330983/305860000000000000000000000000000 : ℝ)*base78 + (1135896323513830983/305860000000000000000000000000000 : ℝ)*base80 + (146126699738069/38232500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (120581/25000000000000000000 : ℝ)*base90 + (120581/25000000000000000000 : ℝ)*base92 + (120581/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (626840793573180511905572157/61172000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1061188371/50000000000000 : ℝ)*(base19) + (1250487451/50000000000000 : ℝ)*(base23) + (122910901/100000000000000 : ℝ)*(upper2) + (33652923/12500000000000 : ℝ)*(upper3) + (44373661/12500000000000 : ℝ)*(upper5) + (394446604510527/20000000000000 : ℝ)*(major0) + (394446604510527/20000000000000 : ℝ)*(major1) + (394446604510527/20000000000000 : ℝ)*(major2) + (8201101067/50000000000000 : ℝ)*(sp1) + (16858426223/100000000000000 : ℝ)*(sp2) + (73702330787241/2500000000000 : ℝ)*(sp4) + (737018676727691/25000000000000 : ℝ)*(sp5) + (1474036936044257/50000000000000 : ℝ)*(sp6) + (249093118010699/25000000000000 : ℝ)*(sp7) + (249093118010699/25000000000000 : ℝ)*(f.failure) + (73702330787241/2500000000000 : ℝ)*(f.sum) + (39745572283623/15293000000000000000000000000 : ℝ)*base66 + (836060468198445281/122344000000000000000000000000000 : ℝ)*base68 + (282379176697069281/122344000000000000000000000000000 : ℝ)*base70 + (769369229636893281/122344000000000000000000000000000 : ℝ)*base72 + (9749749267433/3058600000000000000000000000 : ℝ)*base74 + (22387781942514719/122344000000000000000000000000000 : ℝ)*base75 + (154315786899493281/122344000000000000000000000000000 : ℝ)*base78 + (551898460028210719/122344000000000000000000000000000 : ℝ)*base79 + (9363013621543/7646500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (969833/125000000000000000000 : ℝ)*base89 + (969833/125000000000000000000 : ℝ)*base91 + (969833/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1719_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21599/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3153/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1971/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17287/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1719_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1719_s2_0 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1380113381/10000000000 : ℝ)*x 0 + (136618133/250000000 : ℝ)*x 1 + (1027801479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380113381/10000000000 : ℝ)^5375 ≤ (8659548694881/100000000000000 : ℝ)^4351 := by
    have hnat : (1380113381 : ℕ)^5375*100000000000000^4351 ≤ 8659548694881^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380113381 10000000000 8659548694881 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136618133/250000000 : ℝ)^5375 ≤ (23701483150173/50000000000000 : ℝ)^4351 := by
    have hnat : (136618133 : ℕ)^5375*50000000000000^4351 ≤ 23701483150173^4351*250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136618133 250000000 23701483150173 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027801479/2000000000 : ℝ)^5375 ≤ (43937484991373/100000000000000 : ℝ)^4351 := by
    have hnat : (1027801479 : ℕ)^5375*100000000000000^4351 ≤ 43937484991373^4351*2000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027801479 2000000000 43937484991373 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1380113381/10000000000 : ℝ), (136618133/250000000 : ℝ), (1027801479/2000000000 : ℝ)] ![(8659548694881/100000000000000 : ℝ), (23701483150173/50000000000000 : ℝ), (43937484991373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1380113381/10000000000 : ℝ)|^5375 ≤ (8659548694881/100000000000000 : ℝ)^4351
        have hw : |(-1380113381/10000000000 : ℝ)|=(1380113381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136618133/250000000 : ℝ)|^5375 ≤ (23701483150173/50000000000000 : ℝ)^4351
        have hw : |(136618133/250000000 : ℝ)|=(136618133/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027801479/2000000000 : ℝ)|^5375 ≤ (43937484991373/100000000000000 : ℝ)^4351
        have hw : |(1027801479/2000000000 : ℝ)|=(1027801479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s2_1 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670299561/5000000000 : ℝ)*x 0 + (-1548896071/10000000000 : ℝ)*x 1 + (2569503701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670299561/5000000000 : ℝ)^5375 ≤ (46076424769329/100000000000000 : ℝ)^4351 := by
    have hnat : (2670299561 : ℕ)^5375*100000000000000^4351 ≤ 46076424769329^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670299561 5000000000 46076424769329 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1548896071/10000000000 : ℝ)^5375 ≤ (4993045078047/50000000000000 : ℝ)^4351 := by
    have hnat : (1548896071 : ℕ)^5375*50000000000000^4351 ≤ 4993045078047^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548896071 10000000000 4993045078047 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569503701/5000000000 : ℝ)^5375 ≤ (43937485065307/100000000000000 : ℝ)^4351 := by
    have hnat : (2569503701 : ℕ)^5375*100000000000000^4351 ≤ 43937485065307^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569503701 5000000000 43937485065307 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670299561/5000000000 : ℝ), (-1548896071/10000000000 : ℝ), (2569503701/5000000000 : ℝ)] ![(46076424769329/100000000000000 : ℝ), (4993045078047/50000000000000 : ℝ), (43937485065307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670299561/5000000000 : ℝ)|^5375 ≤ (46076424769329/100000000000000 : ℝ)^4351
        have hw : |(2670299561/5000000000 : ℝ)|=(2670299561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1548896071/10000000000 : ℝ)|^5375 ≤ (4993045078047/50000000000000 : ℝ)^4351
        have hw : |(-1548896071/10000000000 : ℝ)|=(1548896071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569503701/5000000000 : ℝ)|^5375 ≤ (43937485065307/100000000000000 : ℝ)^4351
        have hw : |(2569503701/5000000000 : ℝ)|=(2569503701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s2_2 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340599163/10000000000 : ℝ)*x 0 + (2569503683/5000000000 : ℝ)*x 1 + (-1548896063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340599163/10000000000 : ℝ)^5375 ≤ (4607642520631/10000000000000 : ℝ)^4351 := by
    have hnat : (5340599163 : ℕ)^5375*10000000000000^4351 ≤ 4607642520631^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340599163 10000000000 4607642520631 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569503683/5000000000 : ℝ)^5375 ≤ (10984371171269/25000000000000 : ℝ)^4351 := by
    have hnat : (2569503683 : ℕ)^5375*25000000000000^4351 ≤ 10984371171269^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569503683 5000000000 10984371171269 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1548896063/10000000000 : ℝ)^5375 ≤ (4993045046189/50000000000000 : ℝ)^4351 := by
    have hnat : (1548896063 : ℕ)^5375*50000000000000^4351 ≤ 4993045046189^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548896063 10000000000 4993045046189 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340599163/10000000000 : ℝ), (2569503683/5000000000 : ℝ), (-1548896063/10000000000 : ℝ)] ![(4607642520631/10000000000000 : ℝ), (10984371171269/25000000000000 : ℝ), (4993045046189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340599163/10000000000 : ℝ)|^5375 ≤ (4607642520631/10000000000000 : ℝ)^4351
        have hw : |(5340599163/10000000000 : ℝ)|=(5340599163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569503683/5000000000 : ℝ)|^5375 ≤ (10984371171269/25000000000000 : ℝ)^4351
        have hw : |(2569503683/5000000000 : ℝ)|=(2569503683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1548896063/10000000000 : ℝ)|^5375 ≤ (4993045046189/50000000000000 : ℝ)^4351
        have hw : |(-1548896063/10000000000 : ℝ)|=(1548896063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s2_3 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4093250259/10000000000 : ℝ)*x 0 + (1814453049/5000000000 : ℝ)*x 1 + (4592648907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4093250259/10000000000 : ℝ)^5375 ≤ (16585908919053/50000000000000 : ℝ)^4351 := by
    have hnat : (4093250259 : ℕ)^5375*50000000000000^4351 ≤ 16585908919053^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093250259 10000000000 16585908919053 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1814453049/5000000000 : ℝ)^5375 ≤ (28587076437533/100000000000000 : ℝ)^4351 := by
    have hnat : (1814453049 : ℕ)^5375*100000000000000^4351 ≤ 28587076437533^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814453049 5000000000 28587076437533 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4592648907/10000000000 : ℝ)^5375 ≤ (38241105706111/100000000000000 : ℝ)^4351 := by
    have hnat : (4592648907 : ℕ)^5375*100000000000000^4351 ≤ 38241105706111^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592648907 10000000000 38241105706111 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4093250259/10000000000 : ℝ), (1814453049/5000000000 : ℝ), (4592648907/10000000000 : ℝ)] ![(16585908919053/50000000000000 : ℝ), (28587076437533/100000000000000 : ℝ), (38241105706111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4093250259/10000000000 : ℝ)|^5375 ≤ (16585908919053/50000000000000 : ℝ)^4351
        have hw : |(4093250259/10000000000 : ℝ)|=(4093250259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1814453049/5000000000 : ℝ)|^5375 ≤ (28587076437533/100000000000000 : ℝ)^4351
        have hw : |(1814453049/5000000000 : ℝ)|=(1814453049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4592648907/10000000000 : ℝ)|^5375 ≤ (38241105706111/100000000000000 : ℝ)^4351
        have hw : |(4592648907/10000000000 : ℝ)|=(4592648907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s2_4 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43133129/312500000 : ℝ)*x 0 + (2571325479/5000000000 : ℝ)*x 1 + (1365256833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43133129/312500000 : ℝ)^5375 ≤ (8660686176907/100000000000000 : ℝ)^4351 := by
    have hnat : (43133129 : ℕ)^5375*100000000000000^4351 ≤ 8660686176907^4351*312500000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43133129 312500000 8660686176907 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571325479/5000000000 : ℝ)^5375 ≤ (43975971440663/100000000000000 : ℝ)^4351 := by
    have hnat : (2571325479 : ℕ)^5375*100000000000000^4351 ≤ 43975971440663^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571325479 5000000000 43975971440663 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365256833/2500000000 : ℝ)^5375 ≤ (23681671188529/50000000000000 : ℝ)^4351 := by
    have hnat : (1365256833 : ℕ)^5375*50000000000000^4351 ≤ 23681671188529^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365256833 2500000000 23681671188529 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43133129/312500000 : ℝ), (2571325479/5000000000 : ℝ), (1365256833/2500000000 : ℝ)] ![(8660686176907/100000000000000 : ℝ), (43975971440663/100000000000000 : ℝ), (23681671188529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43133129/312500000 : ℝ)|^5375 ≤ (8660686176907/100000000000000 : ℝ)^4351
        have hw : |(-43133129/312500000 : ℝ)|=(43133129/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571325479/5000000000 : ℝ)|^5375 ≤ (43975971440663/100000000000000 : ℝ)^4351
        have hw : |(2571325479/5000000000 : ℝ)|=(2571325479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365256833/2500000000 : ℝ)|^5375 ≤ (23681671188529/50000000000000 : ℝ)^4351
        have hw : |(1365256833/2500000000 : ℝ)|=(1365256833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s2_5 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253405469/10000000000 : ℝ)*x 0 + (-613437931/5000000000 : ℝ)*x 1 + (2730513781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253405469/10000000000 : ℝ)^5375 ≤ (45148902443309/100000000000000 : ℝ)^4351 := by
    have hnat : (5253405469 : ℕ)^5375*100000000000000^4351 ≤ 45148902443309^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253405469 10000000000 45148902443309 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613437931/5000000000 : ℝ)^5375 ≤ (3743876350409/50000000000000 : ℝ)^4351 := by
    have hnat : (613437931 : ℕ)^5375*50000000000000^4351 ≤ 3743876350409^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613437931 5000000000 3743876350409 50000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730513781/5000000000 : ℝ)^5375 ≤ (4736334484131/10000000000000 : ℝ)^4351 := by
    have hnat : (2730513781 : ℕ)^5375*10000000000000^4351 ≤ 4736334484131^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730513781 5000000000 4736334484131 10000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253405469/10000000000 : ℝ), (-613437931/5000000000 : ℝ), (2730513781/5000000000 : ℝ)] ![(45148902443309/100000000000000 : ℝ), (3743876350409/50000000000000 : ℝ), (4736334484131/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253405469/10000000000 : ℝ)|^5375 ≤ (45148902443309/100000000000000 : ℝ)^4351
        have hw : |(5253405469/10000000000 : ℝ)|=(5253405469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-613437931/5000000000 : ℝ)|^5375 ≤ (3743876350409/50000000000000 : ℝ)^4351
        have hw : |(-613437931/5000000000 : ℝ)|=(613437931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730513781/5000000000 : ℝ)|^5375 ≤ (4736334484131/10000000000000 : ℝ)^4351
        have hw : |(2730513781/5000000000 : ℝ)|=(2730513781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s2_6 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313351333/2500000000 : ℝ)*x 0 + (682628467/1250000000 : ℝ)*x 1 + (-1226875807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313351333/2500000000 : ℝ)^5375 ≤ (45148900988801/100000000000000 : ℝ)^4351 := by
    have hnat : (1313351333 : ℕ)^5375*100000000000000^4351 ≤ 45148900988801^4351*2500000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313351333 2500000000 45148900988801 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682628467/1250000000 : ℝ)^5375 ≤ (47363346705571/100000000000000 : ℝ)^4351 := by
    have hnat : (682628467 : ℕ)^5375*100000000000000^4351 ≤ 47363346705571^4351*1250000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682628467 1250000000 47363346705571 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1226875807/10000000000 : ℝ)^5375 ≤ (1871938071537/25000000000000 : ℝ)^4351 := by
    have hnat : (1226875807 : ℕ)^5375*25000000000000^4351 ≤ 1871938071537^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226875807 10000000000 1871938071537 25000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313351333/2500000000 : ℝ), (682628467/1250000000 : ℝ), (-1226875807/10000000000 : ℝ)] ![(45148900988801/100000000000000 : ℝ), (47363346705571/100000000000000 : ℝ), (1871938071537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313351333/2500000000 : ℝ)|^5375 ≤ (45148900988801/100000000000000 : ℝ)^4351
        have hw : |(1313351333/2500000000 : ℝ)|=(1313351333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682628467/1250000000 : ℝ)|^5375 ≤ (47363346705571/100000000000000 : ℝ)^4351
        have hw : |(682628467/1250000000 : ℝ)|=(682628467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1226875807/10000000000 : ℝ)|^5375 ≤ (1871938071537/25000000000000 : ℝ)^4351
        have hw : |(-1226875807/10000000000 : ℝ)|=(1226875807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1719_s2_7 (p : ℝ) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4093684291/10000000000 : ℝ)*x 0 + (2290934283/5000000000 : ℝ)*x 1 + (363984733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4093684291/10000000000 : ℝ)^5375 ≤ (33176163115719/100000000000000 : ℝ)^4351 := by
    have hnat : (4093684291 : ℕ)^5375*100000000000000^4351 ≤ 33176163115719^4351*10000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093684291 10000000000 33176163115719 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2290934283/5000000000 : ℝ)^5375 ≤ (38130247197767/100000000000000 : ℝ)^4351 := by
    have hnat : (2290934283 : ℕ)^5375*100000000000000^4351 ≤ 38130247197767^4351*5000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290934283 5000000000 38130247197767 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363984733/1000000000 : ℝ)^5375 ≤ (28693589669421/100000000000000 : ℝ)^4351 := by
    have hnat : (363984733 : ℕ)^5375*100000000000000^4351 ≤ 28693589669421^4351*1000000000^5375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363984733 1000000000 28693589669421 100000000000000 5375 4351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5375/1024 : ℝ)) 5375 4351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4093684291/10000000000 : ℝ), (2290934283/5000000000 : ℝ), (363984733/1000000000 : ℝ)] ![(33176163115719/100000000000000 : ℝ), (38130247197767/100000000000000 : ℝ), (28693589669421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4093684291/10000000000 : ℝ)|^5375 ≤ (33176163115719/100000000000000 : ℝ)^4351
        have hw : |(4093684291/10000000000 : ℝ)|=(4093684291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2290934283/5000000000 : ℝ)|^5375 ≤ (38130247197767/100000000000000 : ℝ)^4351
        have hw : |(2290934283/5000000000 : ℝ)|=(2290934283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(363984733/1000000000 : ℝ)|^5375 ≤ (28693589669421/100000000000000 : ℝ)^4351
        have hw : |(363984733/1000000000 : ℝ)|=(363984733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1719_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1971/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1259/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4259/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1971/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1971/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1971/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1971/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1971/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1971/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1971/20000 : ℝ) ^ (5367/1024 : ℝ) ≤ (531547542987557/100000000000000000000 : ℝ) := by
    have hpowers : (1971/20000 : ℝ)^5367 ≤ (531547542987557/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1971 : ℕ)^5367*100000000000000000000^1024 ≤ 531547542987557^1024*20000^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1971 20000 531547542987557 100000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1971/20000 : ℝ)) (X := (531547542987557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17287/100000 : ℝ) ^ (5367/1024 : ℝ) ≤ (10109456264915443/100000000000000000000 : ℝ) := by
    have hpowers : (17287/100000 : ℝ)^5367 ≤ (10109456264915443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17287 : ℕ)^5367*100000000000000000000^1024 ≤ 10109456264915443^1024*100000^5367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17287 100000 10109456264915443 100000000000000000000 5367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17287/100000 : ℝ)) (X := (10109456264915443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000531547542987557/50000000000000000000 : ℝ) ≤ (1250002535412441/1250000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (50000531547542987557/50000000000000000000 : ℝ)^1024 ≤ (1250002535412441/1250000000000000 : ℝ)^5367 := by
      have hnat : (50000531547542987557 : ℕ)^1024*1250000000000000^5367 ≤ 1250002535412441^5367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000531547542987557 50000000000000000000 1250002535412441 1250000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002535412441/1250000000000000 : ℝ)) (X := (50000531547542987557/50000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010641003807903/100000000000000000 : ℝ) ≤ (2000040603386619/2000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (100010641003807903/100000000000000000 : ℝ)^1024 ≤ (2000040603386619/2000000000000000 : ℝ)^5367 := by
      have hnat : (100010641003807903 : ℕ)^1024*2000000000000000^5367 ≤ 2000040603386619^5367*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010641003807903 100000000000000000 2000040603386619 2000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000040603386619/2000000000000000 : ℝ)) (X := (100010641003807903/100000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010109456264915443/50000000000000000000 : ℝ) ≤ (5000192875283331/5000000000000000 : ℝ) ^ (5367/1024 : ℝ) := by
    have hpowers : (50010109456264915443/50000000000000000000 : ℝ)^1024 ≤ (5000192875283331/5000000000000000 : ℝ)^5367 := by
      have hnat : (50010109456264915443 : ℕ)^1024*5000000000000000^5367 ≤ 5000192875283331^5367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010109456264915443 50000000000000000000 5000192875283331 5000000000000000 1024 5367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000192875283331/5000000000000000 : ℝ)) (X := (50010109456264915443/50000000000000000000 : ℝ)) (by norm_num) 5367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(531547542987557/100000000000000000000 : ℝ) ≤ ((37158274532782243263/37160000000000000000 : ℝ)+2*(182733633567/743200000000000 : ℝ)*(1971/20000 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (37158274532782243263/37160000000000000000 : ℝ)+2*(182733633567/743200000000000 : ℝ)*(1971/20000 : ℝ)=(1250002535412441/1250000000000000 : ℝ) by norm_num, show 1+2*(531547542987557/100000000000000000000 : ℝ)=(50000531547542987557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10109456264915443/100000000000000000000 : ℝ)+(531547542987557/100000000000000000000 : ℝ) ≤ ((37158274532782243263/37160000000000000000 : ℝ)+(182733633567/743200000000000 : ℝ)*((17287/100000 : ℝ)+(1971/20000 : ℝ)))^(5367/1024 : ℝ) := by
    rw [show (37158274532782243263/37160000000000000000 : ℝ)+(182733633567/743200000000000 : ℝ)*((17287/100000 : ℝ)+(1971/20000 : ℝ))=(2000040603386619/2000000000000000 : ℝ) by norm_num, show 1+(10109456264915443/100000000000000000000 : ℝ)+(531547542987557/100000000000000000000 : ℝ)=(100010641003807903/100000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10109456264915443/100000000000000000000 : ℝ) ≤ ((37158274532782243263/37160000000000000000 : ℝ)+2*(182733633567/743200000000000 : ℝ)*(17287/100000 : ℝ))^(5367/1024 : ℝ) := by
    rw [show (37158274532782243263/37160000000000000000 : ℝ)+2*(182733633567/743200000000000 : ℝ)*(17287/100000 : ℝ)=(5000192875283331/5000000000000000 : ℝ) by norm_num, show 1+2*(10109456264915443/100000000000000000000 : ℝ)=(50010109456264915443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37158274532782243263/37160000000000000000 : ℝ)*(X 1 0+X 2 0)+(182733633567/743200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (1971/20000 : ℝ)) (hi := (17287/100000 : ℝ)) (c := (37158274532782243263/37160000000000000000 : ℝ)) (alpha := (182733633567/743200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37158274532782243263/37160000000000000000 : ℝ)*(X 0 1+X 2 1)+(182733633567/743200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (1971/20000 : ℝ)) (hi := (17287/100000 : ℝ)) (c := (37158274532782243263/37160000000000000000 : ℝ)) (alpha := (182733633567/743200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37158274532782243263/37160000000000000000 : ℝ)*(X 0 2+X 1 2)+(182733633567/743200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5367/1024 : ℝ)) (lo := (1971/20000 : ℝ)) (hi := (17287/100000 : ℝ)) (c := (37158274532782243263/37160000000000000000 : ℝ)) (alpha := (182733633567/743200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1380113381/10000000000 : ℝ)*X 0 0+(136618133/250000000 : ℝ)*X 0 1+(1027801479/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2670299561/5000000000 : ℝ)*X 1 0+(-1548896071/10000000000 : ℝ)*X 1 1+(2569503701/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5340599163/10000000000 : ℝ)*X 2 0+(2569503683/5000000000 : ℝ)*X 2 1+(-1548896063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4093250259/10000000000 : ℝ)*X 0 0+(1814453049/5000000000 : ℝ)*X 0 1+(4592648907/10000000000 : ℝ)*X 0 2+(4093250259/10000000000 : ℝ)*X 1 0+(1814453049/5000000000 : ℝ)*X 1 1+(4592648907/10000000000 : ℝ)*X 1 2+(4093250259/10000000000 : ℝ)*X 2 0+(1814453049/5000000000 : ℝ)*X 2 1+(4592648907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43133129/312500000 : ℝ)*X 0 0+(2571325479/5000000000 : ℝ)*X 0 1+(1365256833/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253405469/10000000000 : ℝ)*X 1 0+(-613437931/5000000000 : ℝ)*X 1 1+(2730513781/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313351333/2500000000 : ℝ)*X 2 0+(682628467/1250000000 : ℝ)*X 2 1+(-1226875807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4093684291/10000000000 : ℝ)*X 0 0+(2290934283/5000000000 : ℝ)*X 0 1+(363984733/1000000000 : ℝ)*X 0 2+(4093684291/10000000000 : ℝ)*X 1 0+(2290934283/5000000000 : ℝ)*X 1 1+(363984733/1000000000 : ℝ)*X 1 2+(4093684291/10000000000 : ℝ)*X 2 0+(2290934283/5000000000 : ℝ)*X 2 1+(363984733/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1719_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9111684767580842095650775227/929000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1431790631/100000000000000 : ℝ)*(base19) + (1357175143/100000000000000 : ℝ)*(base23) + (52436833/100000000000000 : ℝ)*(lower2) + (235390637/100000000000000 : ℝ)*(upper3) + (86710757/50000000000000 : ℝ)*(upper5) + (2053900650157487/100000000000000 : ℝ)*(major0) + (2053900650157487/100000000000000 : ℝ)*(major1) + (128368790634843/6250000000000 : ℝ)*(major2) + (191884726947667/6250000000000 : ℝ)*(sp0) + (1535084284813333/50000000000000 : ℝ)*(sp1) + (1535084322121077/50000000000000 : ℝ)*(sp2) + (1037625768639689/100000000000000 : ℝ)*(sp3) + (114962037/800000000000 : ℝ)*(sp4) + (1300830689/25000000000000 : ℝ)*(sp7) + (207526194392489/20000000000000 : ℝ)*(f.failure) + (191885625088581/6250000000000 : ℝ)*(f.sum) + (5549074089721/2972800000000000000000000000 : ℝ)*base65 + (6470610466848439919/3716000000000000000000000000000000 : ℝ)*base68 + (8425916831107917/116125000000000000000000000000000 : ℝ)*base69 + (21934727711404439919/3716000000000000000000000000000000 : ℝ)*base72 + (25744189743117/14864000000000000000000000000 : ℝ)*base73 + (1149910072485107917/116125000000000000000000000000000 : ℝ)*base75 + (72714115682789919/3716000000000000000000000000000000 : ℝ)*base78 + (22147408601510789919/3716000000000000000000000000000000 : ℝ)*base80 + (196842676843031/37160000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (929763/100000000000000000000 : ℝ)*base89 + (929763/100000000000000000000 : ℝ)*base91 + (70237/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1243080238735637037519787179/464500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42180031/10000000000000 : ℝ)*(base19) + (73612727/20000000000000 : ℝ)*(base23) + (96430501/100000000000000 : ℝ)*(upper3) + (1029433/50000000000000 : ℝ)*(lower4) + (31901089/100000000000000 : ℝ)*(upper5) + (1050620666310511/50000000000000 : ℝ)*(major0) + (1050620666310511/50000000000000 : ℝ)*(major1) + (1050620666310511/50000000000000 : ℝ)*(major2) + (649280017/12500000000000 : ℝ)*(sp1) + (665555837/10000000000000 : ℝ)*(sp2) + (1570467541457483/50000000000000 : ℝ)*(sp4) + (78523236671863/2500000000000 : ℝ)*(sp5) + (19630800370581/625000000000 : ℝ)*(sp6) + (530773746560729/50000000000000 : ℝ)*(sp7) + (530773746560729/50000000000000 : ℝ)*(f.failure) + (1570467541457483/50000000000000 : ℝ)*(f.sum) + (108443285617337/18580000000000000000000000000 : ℝ)*base65 + (2652179980415312607/1858000000000000000000000000000000 : ℝ)*base68 + (13483448942583312607/1858000000000000000000000000000000 : ℝ)*base70 + (365167955067312607/1858000000000000000000000000000000 : ℝ)*base72 + (63977505094177/18580000000000000000000000000 : ℝ)*base73 + (15020305162183312607/1858000000000000000000000000000000 : ℝ)*base76 + (1944833159831312607/1858000000000000000000000000000000 : ℝ)*base78 + (4686818661968687393/1858000000000000000000000000000000 : ℝ)*base79 + (80562702301063/18580000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (518157/250000000000000000000 : ℝ)*base90 + (518157/250000000000000000000 : ℝ)*base92 + (518157/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1719_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1971/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4259/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1719_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1719_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4259/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1719_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1719_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1719_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5367/1024 : ℝ) ≤ p) (hpb : p ≤ (5375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9897067/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4259/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1719_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
