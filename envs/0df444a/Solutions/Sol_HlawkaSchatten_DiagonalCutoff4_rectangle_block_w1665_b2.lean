-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1665_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:19:04.797351+00:00
-- url     : https://prove2.me/submissions/55646717-0a03-4435-a08b-9d033c69d02a

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
theorem support_rectangle_w1665_box_0 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-661167377/5000000000 : ℝ)*x 0 + (337775053/625000000 : ℝ)*x 1 + (540440077/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661167377/5000000000 : ℝ)^4979 ≤ (7831509601557/100000000000000 : ℝ)^3955 := by
    have hnat : (661167377 : ℕ)^4979*100000000000000^3955 ≤ 7831509601557^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661167377 5000000000 7831509601557 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337775053/625000000 : ℝ)^4979 ≤ (46084245612419/100000000000000 : ℝ)^3955 := by
    have hnat : (337775053 : ℕ)^4979*100000000000000^3955 ≤ 46084245612419^3955*625000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337775053 625000000 46084245612419 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540440077/1000000000 : ℝ)^4979 ≤ (11521061193773/25000000000000 : ℝ)^3955 := by
    have hnat : (540440077 : ℕ)^4979*25000000000000^3955 ≤ 11521061193773^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540440077 1000000000 11521061193773 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-661167377/5000000000 : ℝ), (337775053/625000000 : ℝ), (540440077/1000000000 : ℝ)] ![(7831509601557/100000000000000 : ℝ), (46084245612419/100000000000000 : ℝ), (11521061193773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-661167377/5000000000 : ℝ)|^4979 ≤ (7831509601557/100000000000000 : ℝ)^3955
        have hw : |(-661167377/5000000000 : ℝ)|=(661167377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337775053/625000000 : ℝ)|^4979 ≤ (46084245612419/100000000000000 : ℝ)^3955
        have hw : |(337775053/625000000 : ℝ)|=(337775053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540440077/1000000000 : ℝ)|^4979 ≤ (11521061193773/25000000000000 : ℝ)^3955
        have hw : |(540440077/1000000000 : ℝ)|=(540440077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_1 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250806677/10000000000 : ℝ)*x 0 + (-1538266877/10000000000 : ℝ)*x 1 + (1080880161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250806677/10000000000 : ℝ)^4979 ≤ (1388797726991/3125000000000 : ℝ)^3955 := by
    have hnat : (5250806677 : ℕ)^4979*3125000000000^3955 ≤ 1388797726991^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250806677 10000000000 1388797726991 3125000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1538266877/10000000000 : ℝ)^4979 ≤ (473711378579/5000000000000 : ℝ)^3955 := by
    have hnat : (1538266877 : ℕ)^4979*5000000000000^3955 ≤ 473711378579^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1538266877 10000000000 473711378579 5000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080880161/2000000000 : ℝ)^4979 ≤ (1440132660963/3125000000000 : ℝ)^3955 := by
    have hnat : (1080880161 : ℕ)^4979*3125000000000^3955 ≤ 1440132660963^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080880161 2000000000 1440132660963 3125000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250806677/10000000000 : ℝ), (-1538266877/10000000000 : ℝ), (1080880161/2000000000 : ℝ)] ![(1388797726991/3125000000000 : ℝ), (473711378579/5000000000000 : ℝ), (1440132660963/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250806677/10000000000 : ℝ)|^4979 ≤ (1388797726991/3125000000000 : ℝ)^3955
        have hw : |(5250806677/10000000000 : ℝ)|=(5250806677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1538266877/10000000000 : ℝ)|^4979 ≤ (473711378579/5000000000000 : ℝ)^3955
        have hw : |(-1538266877/10000000000 : ℝ)|=(1538266877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080880161/2000000000 : ℝ)|^4979 ≤ (1440132660963/3125000000000 : ℝ)^3955
        have hw : |(1080880161/2000000000 : ℝ)|=(1080880161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_2 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250806721/10000000000 : ℝ)*x 0 + (5404400773/10000000000 : ℝ)*x 1 + (-769133431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250806721/10000000000 : ℝ)^4979 ≤ (44441527732537/100000000000000 : ℝ)^3955 := by
    have hnat : (5250806721 : ℕ)^4979*100000000000000^3955 ≤ 44441527732537^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250806721 10000000000 44441527732537 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404400773/10000000000 : ℝ)^4979 ≤ (46084244807297/100000000000000 : ℝ)^3955 := by
    have hnat : (5404400773 : ℕ)^4979*100000000000000^3955 ≤ 46084244807297^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404400773 10000000000 46084244807297 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769133431/5000000000 : ℝ)^4979 ≤ (378969098211/4000000000000 : ℝ)^3955 := by
    have hnat : (769133431 : ℕ)^4979*4000000000000^3955 ≤ 378969098211^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769133431 5000000000 378969098211 4000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250806721/10000000000 : ℝ), (5404400773/10000000000 : ℝ), (-769133431/5000000000 : ℝ)] ![(44441527732537/100000000000000 : ℝ), (46084244807297/100000000000000 : ℝ), (378969098211/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250806721/10000000000 : ℝ)|^4979 ≤ (44441527732537/100000000000000 : ℝ)^3955
        have hw : |(5250806721/10000000000 : ℝ)|=(5250806721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404400773/10000000000 : ℝ)|^4979 ≤ (46084244807297/100000000000000 : ℝ)^3955
        have hw : |(5404400773/10000000000 : ℝ)|=(5404400773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-769133431/5000000000 : ℝ)|^4979 ≤ (378969098211/4000000000000 : ℝ)^3955
        have hw : |(-769133431/5000000000 : ℝ)|=(769133431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_3 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (555655821/1250000000 : ℝ)*x 0 + (4043252237/10000000000 : ℝ)*x 1 + (404325221/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (555655821/1250000000 : ℝ)^4979 ≤ (18017793313623/50000000000000 : ℝ)^3955 := by
    have hnat : (555655821 : ℕ)^4979*50000000000000^3955 ≤ 18017793313623^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555655821 1250000000 18017793313623 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4043252237/10000000000 : ℝ)^4979 ≤ (15991103405801/50000000000000 : ℝ)^3955 := by
    have hnat : (4043252237 : ℕ)^4979*50000000000000^3955 ≤ 15991103405801^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043252237 10000000000 15991103405801 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404325221/1000000000 : ℝ)^4979 ≤ (1998887908921/6250000000000 : ℝ)^3955 := by
    have hnat : (404325221 : ℕ)^4979*6250000000000^3955 ≤ 1998887908921^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404325221 1000000000 1998887908921 6250000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(555655821/1250000000 : ℝ), (4043252237/10000000000 : ℝ), (404325221/1000000000 : ℝ)] ![(18017793313623/50000000000000 : ℝ), (15991103405801/50000000000000 : ℝ), (1998887908921/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(555655821/1250000000 : ℝ)|^4979 ≤ (18017793313623/50000000000000 : ℝ)^3955
        have hw : |(555655821/1250000000 : ℝ)|=(555655821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4043252237/10000000000 : ℝ)|^4979 ≤ (15991103405801/50000000000000 : ℝ)^3955
        have hw : |(4043252237/10000000000 : ℝ)|=(4043252237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(404325221/1000000000 : ℝ)|^4979 ≤ (1998887908921/6250000000000 : ℝ)^3955
        have hw : |(404325221/1000000000 : ℝ)|=(404325221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_4 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1838322849/10000000000 : ℝ)*x 0 + (1043210801/2000000000 : ℝ)*x 1 + (5216053731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1838322849/10000000000 : ℝ)^4979 ≤ (2964225245427/25000000000000 : ℝ)^3955 := by
    have hnat : (1838322849 : ℕ)^4979*25000000000000^3955 ≤ 2964225245427^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838322849 10000000000 2964225245427 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043210801/2000000000 : ℝ)^4979 ≤ (8814310192303/20000000000000 : ℝ)^3955 := by
    have hnat : (1043210801 : ℕ)^4979*20000000000000^3955 ≤ 8814310192303^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043210801 2000000000 8814310192303 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216053731/10000000000 : ℝ)^4979 ≤ (22035774023513/50000000000000 : ℝ)^3955 := by
    have hnat : (5216053731 : ℕ)^4979*50000000000000^3955 ≤ 22035774023513^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216053731 10000000000 22035774023513 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1838322849/10000000000 : ℝ), (1043210801/2000000000 : ℝ), (5216053731/10000000000 : ℝ)] ![(2964225245427/25000000000000 : ℝ), (8814310192303/20000000000000 : ℝ), (22035774023513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1838322849/10000000000 : ℝ)|^4979 ≤ (2964225245427/25000000000000 : ℝ)^3955
        have hw : |(-1838322849/10000000000 : ℝ)|=(1838322849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043210801/2000000000 : ℝ)|^4979 ≤ (8814310192303/20000000000000 : ℝ)^3955
        have hw : |(1043210801/2000000000 : ℝ)|=(1043210801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216053731/10000000000 : ℝ)|^4979 ≤ (22035774023513/50000000000000 : ℝ)^3955
        have hw : |(5216053731/10000000000 : ℝ)|=(5216053731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_5 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672478279/1250000000 : ℝ)*x 0 + (-32388781/200000000 : ℝ)*x 1 + (1304013511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672478279/1250000000 : ℝ)^4979 ≤ (9164118695299/20000000000000 : ℝ)^3955 := by
    have hnat : (672478279 : ℕ)^4979*20000000000000^3955 ≤ 9164118695299^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672478279 1250000000 9164118695299 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32388781/200000000 : ℝ)^4979 ≤ (5053927565303/50000000000000 : ℝ)^3955 := by
    have hnat : (32388781 : ℕ)^4979*50000000000000^3955 ≤ 5053927565303^3955*200000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32388781 200000000 5053927565303 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304013511/2500000000 : ℝ)^4979 ≤ (44071551376351/100000000000000 : ℝ)^3955 := by
    have hnat : (1304013511 : ℕ)^4979*100000000000000^3955 ≤ 44071551376351^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304013511 2500000000 44071551376351 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672478279/1250000000 : ℝ), (-32388781/200000000 : ℝ), (1304013511/2500000000 : ℝ)] ![(9164118695299/20000000000000 : ℝ), (5053927565303/50000000000000 : ℝ), (44071551376351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672478279/1250000000 : ℝ)|^4979 ≤ (9164118695299/20000000000000 : ℝ)^3955
        have hw : |(672478279/1250000000 : ℝ)|=(672478279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32388781/200000000 : ℝ)|^4979 ≤ (5053927565303/50000000000000 : ℝ)^3955
        have hw : |(-32388781/200000000 : ℝ)|=(32388781/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304013511/2500000000 : ℝ)|^4979 ≤ (44071551376351/100000000000000 : ℝ)^3955
        have hw : |(1304013511/2500000000 : ℝ)|=(1304013511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_6 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672478331/1250000000 : ℝ)*x 0 + (5216053563/10000000000 : ℝ)*x 1 + (-809719567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672478331/1250000000 : ℝ)^4979 ≤ (45820597936973/100000000000000 : ℝ)^3955 := by
    have hnat : (672478331 : ℕ)^4979*100000000000000^3955 ≤ 45820597936973^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672478331 1250000000 45820597936973 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216053563/10000000000 : ℝ)^4979 ≤ (1101788656501/2500000000000 : ℝ)^3955 := by
    have hnat : (5216053563 : ℕ)^4979*2500000000000^3955 ≤ 1101788656501^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216053563 10000000000 1101788656501 2500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809719567/5000000000 : ℝ)^4979 ≤ (2021571158129/20000000000000 : ℝ)^3955 := by
    have hnat : (809719567 : ℕ)^4979*20000000000000^3955 ≤ 2021571158129^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809719567 5000000000 2021571158129 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672478331/1250000000 : ℝ), (5216053563/10000000000 : ℝ), (-809719567/5000000000 : ℝ)] ![(45820597936973/100000000000000 : ℝ), (1101788656501/2500000000000 : ℝ), (2021571158129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672478331/1250000000 : ℝ)|^4979 ≤ (45820597936973/100000000000000 : ℝ)^3955
        have hw : |(672478331/1250000000 : ℝ)|=(672478331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216053563/10000000000 : ℝ)|^4979 ≤ (1101788656501/2500000000000 : ℝ)^3955
        have hw : |(5216053563/10000000000 : ℝ)|=(5216053563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-809719567/5000000000 : ℝ)|^4979 ≤ (2021571158129/20000000000000 : ℝ)^3955
        have hw : |(-809719567/5000000000 : ℝ)|=(809719567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_7 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (485850149/1250000000 : ℝ)*x 0 + (2161077993/5000000000 : ℝ)*x 1 + (4322155983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485850149/1250000000 : ℝ)^4979 ≤ (1521607165477/5000000000000 : ℝ)^3955 := by
    have hnat : (485850149 : ℕ)^4979*5000000000000^3955 ≤ 1521607165477^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485850149 1250000000 1521607165477 5000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161077993/5000000000 : ℝ)^4979 ≤ (3478392835169/10000000000000 : ℝ)^3955 := by
    have hnat : (2161077993 : ℕ)^4979*10000000000000^3955 ≤ 3478392835169^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161077993 5000000000 3478392835169 10000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4322155983/10000000000 : ℝ)^4979 ≤ (6956785664259/20000000000000 : ℝ)^3955 := by
    have hnat : (4322155983 : ℕ)^4979*20000000000000^3955 ≤ 6956785664259^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322155983 10000000000 6956785664259 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(485850149/1250000000 : ℝ), (2161077993/5000000000 : ℝ), (4322155983/10000000000 : ℝ)] ![(1521607165477/5000000000000 : ℝ), (3478392835169/10000000000000 : ℝ), (6956785664259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(485850149/1250000000 : ℝ)|^4979 ≤ (1521607165477/5000000000000 : ℝ)^3955
        have hw : |(485850149/1250000000 : ℝ)|=(485850149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2161077993/5000000000 : ℝ)|^4979 ≤ (3478392835169/10000000000000 : ℝ)^3955
        have hw : |(2161077993/5000000000 : ℝ)|=(2161077993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4322155983/10000000000 : ℝ)|^4979 ≤ (6956785664259/20000000000000 : ℝ)^3955
        have hw : |(4322155983/10000000000 : ℝ)|=(4322155983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_8 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1728146563/10000000000 : ℝ)*x 0 + (508025559/1000000000 : ℝ)*x 1 + (5433670463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1728146563/10000000000 : ℝ)^4979 ≤ (10969338714189/100000000000000 : ℝ)^3955 := by
    have hnat : (1728146563 : ℕ)^4979*100000000000000^3955 ≤ 10969338714189^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728146563 10000000000 10969338714189 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508025559/1000000000 : ℝ)^4979 ≤ (42631987416901/100000000000000 : ℝ)^3955 := by
    have hnat : (508025559 : ℕ)^4979*100000000000000^3955 ≤ 42631987416901^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508025559 1000000000 42631987416901 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433670463/10000000000 : ℝ)^4979 ≤ (11599668465437/25000000000000 : ℝ)^3955 := by
    have hnat : (5433670463 : ℕ)^4979*25000000000000^3955 ≤ 11599668465437^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433670463 10000000000 11599668465437 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1728146563/10000000000 : ℝ), (508025559/1000000000 : ℝ), (5433670463/10000000000 : ℝ)] ![(10969338714189/100000000000000 : ℝ), (42631987416901/100000000000000 : ℝ), (11599668465437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1728146563/10000000000 : ℝ)|^4979 ≤ (10969338714189/100000000000000 : ℝ)^3955
        have hw : |(-1728146563/10000000000 : ℝ)|=(1728146563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508025559/1000000000 : ℝ)|^4979 ≤ (42631987416901/100000000000000 : ℝ)^3955
        have hw : |(508025559/1000000000 : ℝ)|=(508025559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433670463/10000000000 : ℝ)|^4979 ≤ (11599668465437/25000000000000 : ℝ)^3955
        have hw : |(5433670463/10000000000 : ℝ)|=(5433670463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_9 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615379793/5000000000 : ℝ)*x 0 + (-1525235279/10000000000 : ℝ)*x 1 + (5433670617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615379793/5000000000 : ℝ)^4979 ≤ (5528503582461/12500000000000 : ℝ)^3955 := by
    have hnat : (2615379793 : ℕ)^4979*12500000000000^3955 ≤ 5528503582461^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615379793 5000000000 5528503582461 12500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1525235279/10000000000 : ℝ)^4979 ≤ (9373295803519/100000000000000 : ℝ)^3955 := by
    have hnat : (1525235279 : ℕ)^4979*100000000000000^3955 ≤ 9373295803519^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525235279 10000000000 9373295803519 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433670617/10000000000 : ℝ)^4979 ≤ (23199337758623/50000000000000 : ℝ)^3955 := by
    have hnat : (5433670617 : ℕ)^4979*50000000000000^3955 ≤ 23199337758623^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433670617 10000000000 23199337758623 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615379793/5000000000 : ℝ), (-1525235279/10000000000 : ℝ), (5433670617/10000000000 : ℝ)] ![(5528503582461/12500000000000 : ℝ), (9373295803519/100000000000000 : ℝ), (23199337758623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615379793/5000000000 : ℝ)|^4979 ≤ (5528503582461/12500000000000 : ℝ)^3955
        have hw : |(2615379793/5000000000 : ℝ)|=(2615379793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1525235279/10000000000 : ℝ)|^4979 ≤ (9373295803519/100000000000000 : ℝ)^3955
        have hw : |(-1525235279/10000000000 : ℝ)|=(1525235279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433670617/10000000000 : ℝ)|^4979 ≤ (23199337758623/50000000000000 : ℝ)^3955
        have hw : |(5433670617/10000000000 : ℝ)|=(5433670617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_10 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307689977/2500000000 : ℝ)*x 0 + (2716835191/5000000000 : ℝ)*x 1 + (-1525235163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307689977/2500000000 : ℝ)^4979 ≤ (22114016043621/50000000000000 : ℝ)^3955 := by
    have hnat : (1307689977 : ℕ)^4979*50000000000000^3955 ≤ 22114016043621^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307689977 2500000000 22114016043621 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716835191/5000000000 : ℝ)^4979 ≤ (46398672991/100000000000 : ℝ)^3955 := by
    have hnat : (2716835191 : ℕ)^4979*100000000000^3955 ≤ 46398672991^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716835191 5000000000 46398672991 100000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1525235163/10000000000 : ℝ)^4979 ≤ (9373294906071/100000000000000 : ℝ)^3955 := by
    have hnat : (1525235163 : ℕ)^4979*100000000000000^3955 ≤ 9373294906071^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525235163 10000000000 9373294906071 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307689977/2500000000 : ℝ), (2716835191/5000000000 : ℝ), (-1525235163/10000000000 : ℝ)] ![(22114016043621/50000000000000 : ℝ), (46398672991/100000000000 : ℝ), (9373294906071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307689977/2500000000 : ℝ)|^4979 ≤ (22114016043621/50000000000000 : ℝ)^3955
        have hw : |(1307689977/2500000000 : ℝ)|=(1307689977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716835191/5000000000 : ℝ)|^4979 ≤ (46398672991/100000000000 : ℝ)^3955
        have hw : |(2716835191/5000000000 : ℝ)|=(2716835191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1525235163/10000000000 : ℝ)|^4979 ≤ (9373294906071/100000000000000 : ℝ)^3955
        have hw : |(-1525235163/10000000000 : ℝ)|=(1525235163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_11 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (141551891/312500000 : ℝ)*x 0 + (399983039/1000000000 : ℝ)*x 1 + (124994691/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141551891/312500000 : ℝ)^4979 ≤ (36899175323681/100000000000000 : ℝ)^3955 := by
    have hnat : (141551891 : ℕ)^4979*100000000000000^3955 ≤ 36899175323681^3955*312500000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141551891 312500000 36899175323681 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399983039/1000000000 : ℝ)^4979 ≤ (31550413707479/100000000000000 : ℝ)^3955 := by
    have hnat : (399983039 : ℕ)^4979*100000000000000^3955 ≤ 31550413707479^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399983039 1000000000 31550413707479 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124994691/312500000 : ℝ)^4979 ≤ (31550410946877/100000000000000 : ℝ)^3955 := by
    have hnat : (124994691 : ℕ)^4979*100000000000000^3955 ≤ 31550410946877^3955*312500000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124994691 312500000 31550410946877 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(141551891/312500000 : ℝ), (399983039/1000000000 : ℝ), (124994691/312500000 : ℝ)] ![(36899175323681/100000000000000 : ℝ), (31550413707479/100000000000000 : ℝ), (31550410946877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(141551891/312500000 : ℝ)|^4979 ≤ (36899175323681/100000000000000 : ℝ)^3955
        have hw : |(141551891/312500000 : ℝ)|=(141551891/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(399983039/1000000000 : ℝ)|^4979 ≤ (31550413707479/100000000000000 : ℝ)^3955
        have hw : |(399983039/1000000000 : ℝ)|=(399983039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(124994691/312500000 : ℝ)|^4979 ≤ (31550410946877/100000000000000 : ℝ)^3955
        have hw : |(124994691/312500000 : ℝ)|=(124994691/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_12 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1430571669/10000000000 : ℝ)*x 0 + (345944873/625000000 : ℝ)*x 1 + (1039254579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1430571669/10000000000 : ℝ)^4979 ≤ (8646896838399/100000000000000 : ℝ)^3955 := by
    have hnat : (1430571669 : ℕ)^4979*100000000000000^3955 ≤ 8646896838399^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430571669 10000000000 8646896838399 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345944873/625000000 : ℝ)^4979 ≤ (23745928470687/50000000000000 : ℝ)^3955 := by
    have hnat : (345944873 : ℕ)^4979*50000000000000^3955 ≤ 23745928470687^3955*625000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345944873 625000000 23745928470687 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039254579/2000000000 : ℝ)^4979 ≤ (21930623105061/50000000000000 : ℝ)^3955 := by
    have hnat : (1039254579 : ℕ)^4979*50000000000000^3955 ≤ 21930623105061^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039254579 2000000000 21930623105061 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1430571669/10000000000 : ℝ), (345944873/625000000 : ℝ), (1039254579/2000000000 : ℝ)] ![(8646896838399/100000000000000 : ℝ), (23745928470687/50000000000000 : ℝ), (21930623105061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1430571669/10000000000 : ℝ)|^4979 ≤ (8646896838399/100000000000000 : ℝ)^3955
        have hw : |(-1430571669/10000000000 : ℝ)|=(1430571669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(345944873/625000000 : ℝ)|^4979 ≤ (23745928470687/50000000000000 : ℝ)^3955
        have hw : |(345944873/625000000 : ℝ)|=(345944873/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039254579/2000000000 : ℝ)|^4979 ≤ (21930623105061/50000000000000 : ℝ)^3955
        have hw : |(1039254579/2000000000 : ℝ)|=(1039254579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_13 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393387753/10000000000 : ℝ)*x 0 + (-1627687441/10000000000 : ℝ)*x 1 + (2598136059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393387753/10000000000 : ℝ)^4979 ≤ (1149151291127/2500000000000 : ℝ)^3955 := by
    have hnat : (5393387753 : ℕ)^4979*2500000000000^3955 ≤ 1149151291127^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393387753 10000000000 1149151291127 2500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1627687441/10000000000 : ℝ)^4979 ≤ (10172710387817/100000000000000 : ℝ)^3955 := by
    have hnat : (1627687441 : ℕ)^4979*100000000000000^3955 ≤ 10172710387817^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627687441 10000000000 10172710387817 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598136059/5000000000 : ℝ)^4979 ≤ (21930618976719/50000000000000 : ℝ)^3955 := by
    have hnat : (2598136059 : ℕ)^4979*50000000000000^3955 ≤ 21930618976719^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598136059 5000000000 21930618976719 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393387753/10000000000 : ℝ), (-1627687441/10000000000 : ℝ), (2598136059/5000000000 : ℝ)] ![(1149151291127/2500000000000 : ℝ), (10172710387817/100000000000000 : ℝ), (21930618976719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393387753/10000000000 : ℝ)|^4979 ≤ (1149151291127/2500000000000 : ℝ)^3955
        have hw : |(5393387753/10000000000 : ℝ)|=(5393387753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1627687441/10000000000 : ℝ)|^4979 ≤ (10172710387817/100000000000000 : ℝ)^3955
        have hw : |(-1627687441/10000000000 : ℝ)|=(1627687441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598136059/5000000000 : ℝ)|^4979 ≤ (21930618976719/50000000000000 : ℝ)^3955
        have hw : |(2598136059/5000000000 : ℝ)|=(2598136059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_14 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078677563/2000000000 : ℝ)*x 0 + (5196271847/10000000000 : ℝ)*x 1 + (-1627687723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078677563/2000000000 : ℝ)^4979 ≤ (5745756538787/12500000000000 : ℝ)^3955 := by
    have hnat : (1078677563 : ℕ)^4979*12500000000000^3955 ≤ 5745756538787^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078677563 2000000000 5745756538787 12500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196271847/10000000000 : ℝ)^4979 ≤ (21930617536847/50000000000000 : ℝ)^3955 := by
    have hnat : (5196271847 : ℕ)^4979*50000000000000^3955 ≤ 21930617536847^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196271847 10000000000 21930617536847 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1627687723/10000000000 : ℝ)^4979 ≤ (10172712606577/100000000000000 : ℝ)^3955 := by
    have hnat : (1627687723 : ℕ)^4979*100000000000000^3955 ≤ 10172712606577^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627687723 10000000000 10172712606577 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078677563/2000000000 : ℝ), (5196271847/10000000000 : ℝ), (-1627687723/10000000000 : ℝ)] ![(5745756538787/12500000000000 : ℝ), (21930617536847/50000000000000 : ℝ), (10172712606577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078677563/2000000000 : ℝ)|^4979 ≤ (5745756538787/12500000000000 : ℝ)^3955
        have hw : |(1078677563/2000000000 : ℝ)|=(1078677563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196271847/10000000000 : ℝ)|^4979 ≤ (21930617536847/50000000000000 : ℝ)^3955
        have hw : |(5196271847/10000000000 : ℝ)|=(5196271847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1627687723/10000000000 : ℝ)|^4979 ≤ (10172712606577/100000000000000 : ℝ)^3955
        have hw : |(-1627687723/10000000000 : ℝ)|=(1627687723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_box_15 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (956629717/2500000000 : ℝ)*x 0 + (2175697611/5000000000 : ℝ)*x 1 + (4351395249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956629717/2500000000 : ℝ)^4979 ≤ (29839150245367/100000000000000 : ℝ)^3955 := by
    have hnat : (956629717 : ℕ)^4979*100000000000000^3955 ≤ 29839150245367^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956629717 2500000000 29839150245367 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2175697611/5000000000 : ℝ)^4979 ≤ (219252654559/625000000000 : ℝ)^3955 := by
    have hnat : (2175697611 : ℕ)^4979*625000000000^3955 ≤ 219252654559^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175697611 5000000000 219252654559 625000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4351395249/10000000000 : ℝ)^4979 ≤ (8770106250867/25000000000000 : ℝ)^3955 := by
    have hnat : (4351395249 : ℕ)^4979*25000000000000^3955 ≤ 8770106250867^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351395249 10000000000 8770106250867 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(956629717/2500000000 : ℝ), (2175697611/5000000000 : ℝ), (4351395249/10000000000 : ℝ)] ![(29839150245367/100000000000000 : ℝ), (219252654559/625000000000 : ℝ), (8770106250867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(956629717/2500000000 : ℝ)|^4979 ≤ (29839150245367/100000000000000 : ℝ)^3955
        have hw : |(956629717/2500000000 : ℝ)|=(956629717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2175697611/5000000000 : ℝ)|^4979 ≤ (219252654559/625000000000 : ℝ)^3955
        have hw : |(2175697611/5000000000 : ℝ)|=(2175697611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4351395249/10000000000 : ℝ)|^4979 ≤ (8770106250867/25000000000000 : ℝ)^3955
        have hw : |(4351395249/10000000000 : ℝ)|=(4351395249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1665_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16283/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58787/100000 : ℝ) ∧ (16293/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5523/6250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5373/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5373/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5373/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5373/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5373/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5373/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5373/50000 : ℝ) ^ (4975/1024 : ℝ) ≤ (982609926555909/50000000000000000000 : ℝ) := by
    have hpowers : (5373/50000 : ℝ)^4975 ≤ (982609926555909/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5373 : ℕ)^4975*50000000000000000000^1024 ≤ 982609926555909^1024*50000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5373 50000 982609926555909 50000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5373/50000 : ℝ)) (X := (982609926555909/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8119/50000 : ℝ) ^ (4975/1024 : ℝ) ≤ (584134023572581/4000000000000000000 : ℝ) := by
    have hpowers : (8119/50000 : ℝ)^4975 ≤ (584134023572581/4000000000000000000 : ℝ)^1024 := by
      have hnat : (8119 : ℕ)^4975*4000000000000000000^1024 ≤ 584134023572581^1024*50000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8119 50000 584134023572581 4000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8119/50000 : ℝ)) (X := (584134023572581/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000982609926555909/25000000000000000000 : ℝ) ≤ (2500020224660529/2500000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (25000982609926555909/25000000000000000000 : ℝ)^1024 ≤ (2500020224660529/2500000000000000 : ℝ)^4975 := by
      have hnat : (25000982609926555909 : ℕ)^1024*2500000000000000^4975 ≤ 2500020224660529^4975*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000982609926555909 25000000000000000000 2500020224660529 2500000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500020224660529/2500000000000000 : ℝ)) (X := (25000982609926555909/25000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016568570442426343/100000000000000000000 : ℝ) ≤ (2000068201407087/2000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (100016568570442426343/100000000000000000000 : ℝ)^1024 ≤ (2000068201407087/2000000000000000 : ℝ)^4975 := by
      have hnat : (100016568570442426343 : ℕ)^1024*2000000000000000^4975 ≤ 2000068201407087^4975*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016568570442426343 100000000000000000000 2000068201407087 2000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000068201407087/2000000000000000 : ℝ)) (X := (100016568570442426343/100000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000584134023572581/2000000000000000000 : ℝ) ≤ (5000300557714377/5000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (2000584134023572581/2000000000000000000 : ℝ)^1024 ≤ (5000300557714377/5000000000000000 : ℝ)^4975 := by
      have hnat : (2000584134023572581 : ℕ)^1024*5000000000000000^4975 ≤ 5000300557714377^4975*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000584134023572581 2000000000000000000 5000300557714377 5000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000300557714377/5000000000000000 : ℝ)) (X := (2000584134023572581/2000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(982609926555909/50000000000000000000 : ℝ) ≤ ((13728713511438322281/13730000000000000000 : ℝ)+2*(260108393319/549200000000000 : ℝ)*(5373/50000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (13728713511438322281/13730000000000000000 : ℝ)+2*(260108393319/549200000000000 : ℝ)*(5373/50000 : ℝ)=(2500020224660529/2500000000000000 : ℝ) by norm_num, show 1+2*(982609926555909/50000000000000000000 : ℝ)=(25000982609926555909/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(584134023572581/4000000000000000000 : ℝ)+(982609926555909/50000000000000000000 : ℝ) ≤ ((13728713511438322281/13730000000000000000 : ℝ)+(260108393319/549200000000000 : ℝ)*((8119/50000 : ℝ)+(5373/50000 : ℝ)))^(4975/1024 : ℝ) := by
    rw [show (13728713511438322281/13730000000000000000 : ℝ)+(260108393319/549200000000000 : ℝ)*((8119/50000 : ℝ)+(5373/50000 : ℝ))=(2000068201407087/2000000000000000 : ℝ) by norm_num, show 1+(584134023572581/4000000000000000000 : ℝ)+(982609926555909/50000000000000000000 : ℝ)=(100016568570442426343/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(584134023572581/4000000000000000000 : ℝ) ≤ ((13728713511438322281/13730000000000000000 : ℝ)+2*(260108393319/549200000000000 : ℝ)*(8119/50000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (13728713511438322281/13730000000000000000 : ℝ)+2*(260108393319/549200000000000 : ℝ)*(8119/50000 : ℝ)=(5000300557714377/5000000000000000 : ℝ) by norm_num, show 1+2*(584134023572581/4000000000000000000 : ℝ)=(2000584134023572581/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13728713511438322281/13730000000000000000 : ℝ)*(X 1 0+X 2 0)+(260108393319/549200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (5373/50000 : ℝ)) (hi := (8119/50000 : ℝ)) (c := (13728713511438322281/13730000000000000000 : ℝ)) (alpha := (260108393319/549200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13728713511438322281/13730000000000000000 : ℝ)*(X 0 1+X 2 1)+(260108393319/549200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (5373/50000 : ℝ)) (hi := (8119/50000 : ℝ)) (c := (13728713511438322281/13730000000000000000 : ℝ)) (alpha := (260108393319/549200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13728713511438322281/13730000000000000000 : ℝ)*(X 0 2+X 1 2)+(260108393319/549200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (5373/50000 : ℝ)) (hi := (8119/50000 : ℝ)) (c := (13728713511438322281/13730000000000000000 : ℝ)) (alpha := (260108393319/549200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-661167377/5000000000 : ℝ)*X 0 0+(337775053/625000000 : ℝ)*X 0 1+(540440077/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250806677/10000000000 : ℝ)*X 1 0+(-1538266877/10000000000 : ℝ)*X 1 1+(1080880161/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250806721/10000000000 : ℝ)*X 2 0+(5404400773/10000000000 : ℝ)*X 2 1+(-769133431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((555655821/1250000000 : ℝ)*X 0 0+(4043252237/10000000000 : ℝ)*X 0 1+(404325221/1000000000 : ℝ)*X 0 2+(555655821/1250000000 : ℝ)*X 1 0+(4043252237/10000000000 : ℝ)*X 1 1+(404325221/1000000000 : ℝ)*X 1 2+(555655821/1250000000 : ℝ)*X 2 0+(4043252237/10000000000 : ℝ)*X 2 1+(404325221/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1838322849/10000000000 : ℝ)*X 0 0+(1043210801/2000000000 : ℝ)*X 0 1+(5216053731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((672478279/1250000000 : ℝ)*X 1 0+(-32388781/200000000 : ℝ)*X 1 1+(1304013511/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672478331/1250000000 : ℝ)*X 2 0+(5216053563/10000000000 : ℝ)*X 2 1+(-809719567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((485850149/1250000000 : ℝ)*X 0 0+(2161077993/5000000000 : ℝ)*X 0 1+(4322155983/10000000000 : ℝ)*X 0 2+(485850149/1250000000 : ℝ)*X 1 0+(2161077993/5000000000 : ℝ)*X 1 1+(4322155983/10000000000 : ℝ)*X 1 2+(485850149/1250000000 : ℝ)*X 2 0+(2161077993/5000000000 : ℝ)*X 2 1+(4322155983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1728146563/10000000000 : ℝ)*X 0 0+(508025559/1000000000 : ℝ)*X 0 1+(5433670463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615379793/5000000000 : ℝ)*X 1 0+(-1525235279/10000000000 : ℝ)*X 1 1+(5433670617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307689977/2500000000 : ℝ)*X 2 0+(2716835191/5000000000 : ℝ)*X 2 1+(-1525235163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((141551891/312500000 : ℝ)*X 0 0+(399983039/1000000000 : ℝ)*X 0 1+(124994691/312500000 : ℝ)*X 0 2+(141551891/312500000 : ℝ)*X 1 0+(399983039/1000000000 : ℝ)*X 1 1+(124994691/312500000 : ℝ)*X 1 2+(141551891/312500000 : ℝ)*X 2 0+(399983039/1000000000 : ℝ)*X 2 1+(124994691/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1430571669/10000000000 : ℝ)*X 0 0+(345944873/625000000 : ℝ)*X 0 1+(1039254579/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5393387753/10000000000 : ℝ)*X 1 0+(-1627687441/10000000000 : ℝ)*X 1 1+(2598136059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1078677563/2000000000 : ℝ)*X 2 0+(5196271847/10000000000 : ℝ)*X 2 1+(-1627687723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((956629717/2500000000 : ℝ)*X 0 0+(2175697611/5000000000 : ℝ)*X 0 1+(4351395249/10000000000 : ℝ)*X 0 2+(956629717/2500000000 : ℝ)*X 1 0+(2175697611/5000000000 : ℝ)*X 1 1+(4351395249/10000000000 : ℝ)*X 1 2+(956629717/2500000000 : ℝ)*X 2 0+(2175697611/5000000000 : ℝ)*X 2 1+(4351395249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16283/25000 : ℝ) ≤ (-447116743564599971448070144660917/686500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68873/1250000000000 : ℝ)*(lower2) + (23385989/100000000000000 : ℝ)*(upper4) + (2775581/10000000000000 : ℝ)*(upper5) + (1787341990761227/100000000000000 : ℝ)*(major0) + (1787341990761227/100000000000000 : ℝ)*(major1) + (1787341990761227/100000000000000 : ℝ)*(major2) + (5391826123/100000000000000 : ℝ)*(sp2) + (39126987/5000000000000 : ℝ)*(sp3) + (326663696856969/12500000000000 : ℝ)*(sp4) + (2613305086248439/100000000000000 : ℝ)*(sp5) + (326663406818089/12500000000000 : ℝ)*(sp6) + (983080518310567/100000000000000 : ℝ)*(sp7) + (3071515083/100000000000000 : ℝ)*(sp8) + (1890030599/25000000000000 : ℝ)*(sp13) + (983081300850307/100000000000000 : ℝ)*(f.failure) + (1306656323185417/50000000000000 : ℝ)*(f.sum) + (2514121809807/27460000000000000000000000000 : ℝ)*base66 + (7350027390150676213/1373000000000000000000000000000000 : ℝ)*base68 + (6666065696440676213/1373000000000000000000000000000000 : ℝ)*base70 + (5627767835054676213/1373000000000000000000000000000000 : ℝ)*base72 + (85490274263347/27460000000000000000000000000 : ℝ)*base74 + (9239462987259676213/1373000000000000000000000000000000 : ℝ)*base76 + (4897592736633676213/1373000000000000000000000000000000 : ℝ)*base78 + (3637780294615676213/1373000000000000000000000000000000 : ℝ)*base80 + (8170368857007/27460000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (78078637/10000000000000000000000 : ℝ)*base89 + (78078637/10000000000000000000000 : ℝ)*base91 + (78078637/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58787/100000 : ℝ) ≤ (201795752524537944368342540585727/343250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (523/24414062500 : ℝ)*(lower1) + (8363/4000000000000 : ℝ)*(lower2) + (10307801/100000000000000 : ℝ)*(upper4) + (1879869565309489/100000000000000 : ℝ)*(major0) + (1879869565309489/100000000000000 : ℝ)*(major1) + (1879869565309489/100000000000000 : ℝ)*(major2) + (1353084062868413/50000000000000 : ℝ)*(sp0) + (1353084286697551/50000000000000 : ℝ)*(sp1) + (1353084340575921/50000000000000 : ℝ)*(sp2) + (258493371628489/25000000000000 : ℝ)*(sp3) + (27659217/10000000000000 : ℝ)*(sp5) + (16883543/10000000000000 : ℝ)*(sp6) + (54258387/25000000000000 : ℝ)*(sp7) + (362125223/50000000000000 : ℝ)*(sp8) + (1033973703547503/100000000000000 : ℝ)*(f.failure) + (338271106248409/12500000000000 : ℝ)*(f.sum) + (216149946978129/27460000000000000000000000000 : ℝ)*base66 + (1157188308265199409/1373000000000000000000000000000000 : ℝ)*base67 + (957277651536800591/1373000000000000000000000000000000 : ℝ)*base70 + (2093158843524800591/1373000000000000000000000000000000 : ℝ)*base72 + (115562281593169/27460000000000000000000000000 : ℝ)*base74 + (3981392630392800591/1373000000000000000000000000000000 : ℝ)*base76 + (9731390193568800591/1373000000000000000000000000000000 : ℝ)*base78 + (1227148893998800591/1373000000000000000000000000000000 : ℝ)*base80 + (115269010825209/27460000000000000000000000000 : ℝ)*base82 + (1996927/10000000000000000000000 : ℝ)*base90 + (1996927/10000000000000000000000 : ℝ)*base92 + (1996927/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (16293/20000 : ℝ) ≤ (69909374977870769442471186066339/85812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13194957/20000000000000 : ℝ)*(lower3) + (37772999/50000000000000 : ℝ)*(upper4) + (26579711/50000000000000 : ℝ)*(lower5) + (246271203093391/12500000000000 : ℝ)*(major0) + (246271203093391/12500000000000 : ℝ)*(major1) + (246271203093391/12500000000000 : ℝ)*(major2) + (5166452857/100000000000000 : ℝ)*(sp0) + (21296991599/50000000000000 : ℝ)*(sp1) + (34830113163/100000000000000 : ℝ)*(sp2) + (26940130717/100000000000000 : ℝ)*(sp3) + (565907460177787/20000000000000 : ℝ)*(sp8) + (1414749936679297/50000000000000 : ℝ)*(sp9) + (707376909307157/25000000000000 : ℝ)*(sp10) + (1083613978956777/100000000000000 : ℝ)*(sp11) + (541820459543747/50000000000000 : ℝ)*(f.failure) + (88423202104431/3125000000000 : ℝ)*(f.sum) + (29995676707553/6865000000000000000000000000 : ℝ)*base65 + (1263357890943255129/171625000000000000000000000000000 : ℝ)*base68 + (1023270656244755129/171625000000000000000000000000000 : ℝ)*base70 + (817489504523880129/171625000000000000000000000000000 : ℝ)*base72 + (8383106410297/6865000000000000000000000000 : ℝ)*base74 + (758518514705880129/171625000000000000000000000000000 : ℝ)*base76 + (367492121291505129/171625000000000000000000000000000 : ℝ)*base78 + (26808606175380129/171625000000000000000000000000000 : ℝ)*base80 + (2757819020401/3432500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (14925677/5000000000000000000000 : ℝ)*base89 + (14925677/5000000000000000000000 : ℝ)*base91 + (14925677/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-5523/6250 : ℝ) ≤ (-30331314020312119062720747754863/34325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137388011/100000000000000 : ℝ)*(upper3) + (46546541/100000000000000 : ℝ)*(lower4) + (4830277/5000000000000 : ℝ)*(upper5) + (201503934272641/10000000000000 : ℝ)*(major0) + (201503934272641/10000000000000 : ℝ)*(major1) + (201503934272641/10000000000000 : ℝ)*(major2) + (10487709537/100000000000000 : ℝ)*(sp4) + (6120531041/3125000000000 : ℝ)*(sp5) + (243678097231/100000000000000 : ℝ)*(sp6) + (17351151059/20000000000000 : ℝ)*(sp7) + (1475601438043301/50000000000000 : ℝ)*(sp12) + (737754376700707/25000000000000 : ℝ)*(sp13) + (737742421424727/25000000000000 : ℝ)*(sp14) + (69264599554337/6250000000000 : ℝ)*(sp15) + (1108320348624687/100000000000000 : ℝ)*(f.failure) + (2951213363796139/100000000000000 : ℝ)*(f.sum) + (7860579247291/2746000000000000000000000000 : ℝ)*base66 + (353965660666489121/137300000000000000000000000000000 : ℝ)*base67 + (646801487626989121/137300000000000000000000000000000 : ℝ)*base69 + (454569936181210879/137300000000000000000000000000000 : ℝ)*base72 + (594014919437/2746000000000000000000000000 : ℝ)*base74 + (998273273183489121/137300000000000000000000000000000 : ℝ)*base75 + (895405974186789121/137300000000000000000000000000000 : ℝ)*base77 + (494393806658089121/137300000000000000000000000000000 : ℝ)*base79 + (3933645224151/2746000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (69214783/10000000000000000000000 : ℝ)*base90 + (69214783/10000000000000000000000 : ℝ)*base92 + (69214783/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1665_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16283/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58787/100000 : ℝ) else (16293/20000 : ℝ) ≤ X j i ∧ X j i ≤ (5523/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1665_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1665_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16283/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58787/100000 : ℝ) else (16293/20000 : ℝ) ≤ X j i ∧ X j i ≤ (5523/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1665_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16283/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58787/100000 : ℝ) else (16293/20000 : ℝ) ≤ X j i ∧ X j i ≤ (5523/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1665_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
