-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1041_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:47:33.617754+00:00
-- url     : https://prove2.me/submissions/298f42f4-e136-4cfa-8b42-2d7cb9feeb09

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
theorem support_rectangle_w1041_s9_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-88645703/400000000 : ℝ)*x 0 + (1348691369/2500000000 : ℝ)*x 1 + (526400591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88645703/400000000 : ℝ)^4117 ≤ (13456887543779/100000000000000 : ℝ)^3093 := by
    have hnat : (88645703 : ℕ)^4117*100000000000000^3093 ≤ 13456887543779^3093*400000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88645703 400000000 13456887543779 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348691369/2500000000 : ℝ)^4117 ≤ (4397812260541/10000000000000 : ℝ)^3093 := by
    have hnat : (1348691369 : ℕ)^4117*10000000000000^3093 ≤ 4397812260541^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348691369 2500000000 4397812260541 10000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526400591/1000000000 : ℝ)^4117 ≤ (42564989840113/100000000000000 : ℝ)^3093 := by
    have hnat : (526400591 : ℕ)^4117*100000000000000^3093 ≤ 42564989840113^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526400591 1000000000 42564989840113 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88645703/400000000 : ℝ), (1348691369/2500000000 : ℝ), (526400591/1000000000 : ℝ)] ![(13456887543779/100000000000000 : ℝ), (4397812260541/10000000000000 : ℝ), (42564989840113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88645703/400000000 : ℝ)|^4117 ≤ (13456887543779/100000000000000 : ℝ)^3093
        have hw : |(-88645703/400000000 : ℝ)|=(88645703/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348691369/2500000000 : ℝ)|^4117 ≤ (4397812260541/10000000000000 : ℝ)^3093
        have hw : |(1348691369/2500000000 : ℝ)|=(1348691369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526400591/1000000000 : ℝ)|^4117 ≤ (42564989840113/100000000000000 : ℝ)^3093
        have hw : |(526400591/1000000000 : ℝ)|=(526400591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s9_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345023461/10000000000 : ℝ)*x 0 + (-2282492469/10000000000 : ℝ)*x 1 + (658000777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345023461/10000000000 : ℝ)^4117 ≤ (43439203356781/100000000000000 : ℝ)^3093 := by
    have hnat : (5345023461 : ℕ)^4117*100000000000000^3093 ≤ 43439203356781^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345023461 10000000000 43439203356781 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282492469/10000000000 : ℝ)^4117 ≤ (13995803494271/100000000000000 : ℝ)^3093 := by
    have hnat : (2282492469 : ℕ)^4117*100000000000000^3093 ≤ 13995803494271^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282492469 10000000000 13995803494271 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658000777/1250000000 : ℝ)^4117 ≤ (2128249656681/5000000000000 : ℝ)^3093 := by
    have hnat : (658000777 : ℕ)^4117*5000000000000^3093 ≤ 2128249656681^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658000777 1250000000 2128249656681 5000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345023461/10000000000 : ℝ), (-2282492469/10000000000 : ℝ), (658000777/1250000000 : ℝ)] ![(43439203356781/100000000000000 : ℝ), (13995803494271/100000000000000 : ℝ), (2128249656681/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345023461/10000000000 : ℝ)|^4117 ≤ (43439203356781/100000000000000 : ℝ)^3093
        have hw : |(5345023461/10000000000 : ℝ)|=(5345023461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282492469/10000000000 : ℝ)|^4117 ≤ (13995803494271/100000000000000 : ℝ)^3093
        have hw : |(-2282492469/10000000000 : ℝ)|=(2282492469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658000777/1250000000 : ℝ)|^4117 ≤ (2128249656681/5000000000000 : ℝ)^3093
        have hw : |(658000777/1250000000 : ℝ)|=(658000777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s9_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345023931/10000000000 : ℝ)*x 0 + (5264005871/10000000000 : ℝ)*x 1 + (-22824923/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345023931/10000000000 : ℝ)^4117 ≤ (43439208441079/100000000000000 : ℝ)^3093 := by
    have hnat : (5345023931 : ℕ)^4117*100000000000000^3093 ≤ 43439208441079^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345023931 10000000000 43439208441079 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264005871/10000000000 : ℝ)^4117 ≤ (665077959693/1562500000000 : ℝ)^3093 := by
    have hnat : (5264005871 : ℕ)^4117*1562500000000^3093 ≤ 665077959693^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264005871 10000000000 665077959693 1562500000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22824923/100000000 : ℝ)^4117 ≤ (2799160422983/20000000000000 : ℝ)^3093 := by
    have hnat : (22824923 : ℕ)^4117*20000000000000^3093 ≤ 2799160422983^3093*100000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22824923 100000000 2799160422983 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345023931/10000000000 : ℝ), (5264005871/10000000000 : ℝ), (-22824923/100000000 : ℝ)] ![(43439208441079/100000000000000 : ℝ), (665077959693/1562500000000 : ℝ), (2799160422983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345023931/10000000000 : ℝ)|^4117 ≤ (43439208441079/100000000000000 : ℝ)^3093
        have hw : |(5345023931/10000000000 : ℝ)|=(5345023931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264005871/10000000000 : ℝ)|^4117 ≤ (665077959693/1562500000000 : ℝ)^3093
        have hw : |(5264005871/10000000000 : ℝ)|=(5264005871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22824923/100000000 : ℝ)|^4117 ≤ (2799160422983/20000000000000 : ℝ)^3093
        have hw : |(-22824923/100000000 : ℝ)|=(22824923/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s9_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2189550609/5000000000 : ℝ)*x 0 + (4253493621/10000000000 : ℝ)*x 1 + (4508491959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189550609/5000000000 : ℝ)^4117 ≤ (33316414237857/100000000000000 : ℝ)^3093 := by
    have hnat : (2189550609 : ℕ)^4117*100000000000000^3093 ≤ 33316414237857^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189550609 5000000000 33316414237857 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253493621/10000000000 : ℝ)^4117 ≤ (1602524207613/5000000000000 : ℝ)^3093 := by
    have hnat : (4253493621 : ℕ)^4117*5000000000000^3093 ≤ 1602524207613^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253493621 10000000000 1602524207613 5000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508491959/10000000000 : ℝ)^4117 ≤ (34633101599281/100000000000000 : ℝ)^3093 := by
    have hnat : (4508491959 : ℕ)^4117*100000000000000^3093 ≤ 34633101599281^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508491959 10000000000 34633101599281 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189550609/5000000000 : ℝ), (4253493621/10000000000 : ℝ), (4508491959/10000000000 : ℝ)] ![(33316414237857/100000000000000 : ℝ), (1602524207613/5000000000000 : ℝ), (34633101599281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189550609/5000000000 : ℝ)|^4117 ≤ (33316414237857/100000000000000 : ℝ)^3093
        have hw : |(2189550609/5000000000 : ℝ)|=(2189550609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253493621/10000000000 : ℝ)|^4117 ≤ (1602524207613/5000000000000 : ℝ)^3093
        have hw : |(4253493621/10000000000 : ℝ)|=(4253493621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508491959/10000000000 : ℝ)|^4117 ≤ (34633101599281/100000000000000 : ℝ)^3093
        have hw : |(4508491959/10000000000 : ℝ)|=(4508491959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s9_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216147683/10000000000 : ℝ)*x 0 + (5264333151/10000000000 : ℝ)*x 1 + (539443707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216147683/10000000000 : ℝ)^4117 ≤ (1345692882941/10000000000000 : ℝ)^3093 := by
    have hnat : (2216147683 : ℕ)^4117*10000000000000^3093 ≤ 1345692882941^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216147683 10000000000 1345692882941 10000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264333151/10000000000 : ℝ)^4117 ≤ (10642128000459/25000000000000 : ℝ)^3093 := by
    have hnat : (5264333151 : ℕ)^4117*25000000000000^3093 ≤ 10642128000459^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264333151 10000000000 10642128000459 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539443707/1000000000 : ℝ)^4117 ≤ (43974559146381/100000000000000 : ℝ)^3093 := by
    have hnat : (539443707 : ℕ)^4117*100000000000000^3093 ≤ 43974559146381^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539443707 1000000000 43974559146381 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216147683/10000000000 : ℝ), (5264333151/10000000000 : ℝ), (539443707/1000000000 : ℝ)] ![(1345692882941/10000000000000 : ℝ), (10642128000459/25000000000000 : ℝ), (43974559146381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216147683/10000000000 : ℝ)|^4117 ≤ (1345692882941/10000000000000 : ℝ)^3093
        have hw : |(-2216147683/10000000000 : ℝ)|=(2216147683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264333151/10000000000 : ℝ)|^4117 ≤ (10642128000459/25000000000000 : ℝ)^3093
        have hw : |(5264333151/10000000000 : ℝ)|=(5264333151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539443707/1000000000 : ℝ)|^4117 ≤ (43974559146381/100000000000000 : ℝ)^3093
        have hw : |(539443707/1000000000 : ℝ)|=(539443707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s9_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656077141/5000000000 : ℝ)*x 0 + (-2152061191/10000000000 : ℝ)*x 1 + (539443707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656077141/5000000000 : ℝ)^4117 ≤ (43083998321813/100000000000000 : ℝ)^3093 := by
    have hnat : (2656077141 : ℕ)^4117*100000000000000^3093 ≤ 43083998321813^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656077141 5000000000 43083998321813 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152061191/10000000000 : ℝ)^4117 ≤ (258828850381/2000000000000 : ℝ)^3093 := by
    have hnat : (2152061191 : ℕ)^4117*2000000000000^3093 ≤ 258828850381^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152061191 10000000000 258828850381 2000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539443707/1000000000 : ℝ)^4117 ≤ (43974559146381/100000000000000 : ℝ)^3093 := by
    have hnat : (539443707 : ℕ)^4117*100000000000000^3093 ≤ 43974559146381^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539443707 1000000000 43974559146381 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656077141/5000000000 : ℝ), (-2152061191/10000000000 : ℝ), (539443707/1000000000 : ℝ)] ![(43083998321813/100000000000000 : ℝ), (258828850381/2000000000000 : ℝ), (43974559146381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656077141/5000000000 : ℝ)|^4117 ≤ (43083998321813/100000000000000 : ℝ)^3093
        have hw : |(2656077141/5000000000 : ℝ)|=(2656077141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2152061191/10000000000 : ℝ)|^4117 ≤ (258828850381/2000000000000 : ℝ)^3093
        have hw : |(-2152061191/10000000000 : ℝ)|=(2152061191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539443707/1000000000 : ℝ)|^4117 ≤ (43974559146381/100000000000000 : ℝ)^3093
        have hw : |(539443707/1000000000 : ℝ)|=(539443707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s9_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875822233/2000000000 : ℝ)*x 0 + (4507854313/10000000000 : ℝ)*x 1 + (2127066801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875822233/2000000000 : ℝ)^4117 ≤ (6663302993927/20000000000000 : ℝ)^3093 := by
    have hnat : (875822233 : ℕ)^4117*20000000000000^3093 ≤ 6663302993927^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875822233 2000000000 6663302993927 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507854313/10000000000 : ℝ)^4117 ≤ (17313290927921/50000000000000 : ℝ)^3093 := by
    have hnat : (4507854313 : ℕ)^4117*50000000000000^3093 ≤ 17313290927921^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507854313 10000000000 17313290927921 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127066801/5000000000 : ℝ)^4117 ≤ (641138063127/2000000000000 : ℝ)^3093 := by
    have hnat : (2127066801 : ℕ)^4117*2000000000000^3093 ≤ 641138063127^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127066801 5000000000 641138063127 2000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875822233/2000000000 : ℝ), (4507854313/10000000000 : ℝ), (2127066801/5000000000 : ℝ)] ![(6663302993927/20000000000000 : ℝ), (17313290927921/50000000000000 : ℝ), (641138063127/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875822233/2000000000 : ℝ)|^4117 ≤ (6663302993927/20000000000000 : ℝ)^3093
        have hw : |(875822233/2000000000 : ℝ)|=(875822233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507854313/10000000000 : ℝ)|^4117 ≤ (17313290927921/50000000000000 : ℝ)^3093
        have hw : |(4507854313/10000000000 : ℝ)|=(4507854313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2127066801/5000000000 : ℝ)|^4117 ≤ (641138063127/2000000000000 : ℝ)^3093
        have hw : |(2127066801/5000000000 : ℝ)|=(2127066801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11217/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (701/6250 : ℝ) ^ (8233/2048 : ℝ) ≤ (3786781208612281/25000000000000000000 : ℝ) := by
    have hpowers : (701/6250 : ℝ)^8233 ≤ (3786781208612281/25000000000000000000 : ℝ)^2048 := by
      have hnat : (701 : ℕ)^8233*25000000000000000000^2048 ≤ 3786781208612281^2048*6250^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 6250 3786781208612281 25000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/6250 : ℝ)) (X := (3786781208612281/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13987/100000 : ℝ) ^ (8233/2048 : ℝ) ≤ (18397809188367643/50000000000000000000 : ℝ) := by
    have hpowers : (13987/100000 : ℝ)^8233 ≤ (18397809188367643/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13987 : ℕ)^8233*50000000000000000000^2048 ≤ 18397809188367643^2048*100000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13987 100000 18397809188367643 50000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13987/100000 : ℝ)) (X := (18397809188367643/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503786781208612281/12500000000000000000 : ℝ) ≤ (5000376749451081/5000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (12503786781208612281/12500000000000000000 : ℝ)^2048 ≤ (5000376749451081/5000000000000000 : ℝ)^8233 := by
      have hnat : (12503786781208612281 : ℕ)^2048*5000000000000000^8233 ≤ 5000376749451081^8233*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503786781208612281 12500000000000000000 5000376749451081 5000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000376749451081/5000000000000000 : ℝ)) (X := (12503786781208612281/12500000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005194274321118441/10000000000000000000 : ℝ) ≤ (10001291849738589/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (10005194274321118441/10000000000000000000 : ℝ)^2048 ≤ (10001291849738589/10000000000000000 : ℝ)^8233 := by
      have hnat : (10005194274321118441 : ℕ)^2048*10000000000000000^8233 ≤ 10001291849738589^8233*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005194274321118441 10000000000000000000 10001291849738589 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001291849738589/10000000000000000 : ℝ)) (X := (10005194274321118441/10000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018397809188367643/25000000000000000000 : ℝ) ≤ (1250228775071877/1250000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (25018397809188367643/25000000000000000000 : ℝ)^2048 ≤ (1250228775071877/1250000000000000 : ℝ)^8233 := by
      have hnat : (25018397809188367643 : ℕ)^2048*1250000000000000^8233 ≤ 1250228775071877^8233*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018397809188367643 25000000000000000000 1250228775071877 1250000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250228775071877/1250000000000000 : ℝ)) (X := (25018397809188367643/25000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3786781208612281/25000000000000000000 : ℝ) ≤ ((13850005829747580219/13855000000000000000 : ℝ)+2*(538350836427/277100000000000 : ℝ)*(701/6250 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (13850005829747580219/13855000000000000000 : ℝ)+2*(538350836427/277100000000000 : ℝ)*(701/6250 : ℝ)=(5000376749451081/5000000000000000 : ℝ) by norm_num, show 1+2*(3786781208612281/25000000000000000000 : ℝ)=(12503786781208612281/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18397809188367643/50000000000000000000 : ℝ)+(3786781208612281/25000000000000000000 : ℝ) ≤ ((13850005829747580219/13855000000000000000 : ℝ)+(538350836427/277100000000000 : ℝ)*((13987/100000 : ℝ)+(701/6250 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (13850005829747580219/13855000000000000000 : ℝ)+(538350836427/277100000000000 : ℝ)*((13987/100000 : ℝ)+(701/6250 : ℝ))=(10001291849738589/10000000000000000 : ℝ) by norm_num, show 1+(18397809188367643/50000000000000000000 : ℝ)+(3786781208612281/25000000000000000000 : ℝ)=(10005194274321118441/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18397809188367643/50000000000000000000 : ℝ) ≤ ((13850005829747580219/13855000000000000000 : ℝ)+2*(538350836427/277100000000000 : ℝ)*(13987/100000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (13850005829747580219/13855000000000000000 : ℝ)+2*(538350836427/277100000000000 : ℝ)*(13987/100000 : ℝ)=(1250228775071877/1250000000000000 : ℝ) by norm_num, show 1+2*(18397809188367643/50000000000000000000 : ℝ)=(25018397809188367643/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13850005829747580219/13855000000000000000 : ℝ)*(X 1 0+X 2 0)+(538350836427/277100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (13850005829747580219/13855000000000000000 : ℝ)) (alpha := (538350836427/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13850005829747580219/13855000000000000000 : ℝ)*(X 0 1+X 2 1)+(538350836427/277100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (13850005829747580219/13855000000000000000 : ℝ)) (alpha := (538350836427/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13850005829747580219/13855000000000000000 : ℝ)*(X 0 2+X 1 2)+(538350836427/277100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (13850005829747580219/13855000000000000000 : ℝ)) (alpha := (538350836427/277100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88645703/400000000 : ℝ)*X 0 0+(1348691369/2500000000 : ℝ)*X 0 1+(526400591/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345023461/10000000000 : ℝ)*X 1 0+(-2282492469/10000000000 : ℝ)*X 1 1+(658000777/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345023931/10000000000 : ℝ)*X 2 0+(5264005871/10000000000 : ℝ)*X 2 1+(-22824923/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2189550609/5000000000 : ℝ)*X 0 0+(4253493621/10000000000 : ℝ)*X 0 1+(4508491959/10000000000 : ℝ)*X 0 2+(2189550609/5000000000 : ℝ)*X 1 0+(4253493621/10000000000 : ℝ)*X 1 1+(4508491959/10000000000 : ℝ)*X 1 2+(2189550609/5000000000 : ℝ)*X 2 0+(4253493621/10000000000 : ℝ)*X 2 1+(4508491959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2216147683/10000000000 : ℝ)*X 0 0+(5264333151/10000000000 : ℝ)*X 0 1+(539443707/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656077141/5000000000 : ℝ)*X 1 0+(-2152061191/10000000000 : ℝ)*X 1 1+(539443707/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((875822233/2000000000 : ℝ)*X 0 0+(4507854313/10000000000 : ℝ)*X 0 1+(2127066801/5000000000 : ℝ)*X 0 2+(875822233/2000000000 : ℝ)*X 1 0+(4507854313/10000000000 : ℝ)*X 1 1+(2127066801/5000000000 : ℝ)*X 1 2+(875822233/2000000000 : ℝ)*X 2 0+(4507854313/10000000000 : ℝ)*X 2 1+(2127066801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (141796490065713896169998259/20375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123380683/20000000000000 : ℝ)*(base19) + (589882243/50000000000000 : ℝ)*(base23) + (11760047/20000000000000 : ℝ)*(lower2) + (19282971/6250000000000 : ℝ)*(upper5) + (5784645020059421/100000000000000 : ℝ)*(major0) + (5784645020059421/100000000000000 : ℝ)*(major1) + (5784645020059421/100000000000000 : ℝ)*(major2) + (7647640789816913/100000000000000 : ℝ)*(sp0) + (955960064352027/12500000000000 : ℝ)*(sp1) + (477980000987199/6250000000000 : ℝ)*(sp2) + (1960801198409487/50000000000000 : ℝ)*(sp3) + (20202871379/50000000000000 : ℝ)*(sp4) + (1596001/2500000000000 : ℝ)*(sp5) + (6215762289/100000000000000 : ℝ)*(sp6) + (3921608612581263/100000000000000 : ℝ)*(f.failure) + (764768119555967/10000000000000 : ℝ)*(f.sum) + (58368339354327/13855000000000000000000000000 : ℝ)*base65 + (8852312859340956801/1385500000000000000000000000000000 : ℝ)*base68 + (11287416868225543199/1385500000000000000000000000000000 : ℝ)*base69 + (2192853631741043199/1385500000000000000000000000000000 : ℝ)*base71 + (67475676266991/6927500000000000000000000000 : ℝ)*base73 + (15501156631032543199/1385500000000000000000000000000000 : ℝ)*base75 + (13273731479537043199/1385500000000000000000000000000000 : ℝ)*base77 + (25814754794120043199/1385500000000000000000000000000000 : ℝ)*base79 + (4744171619853/13855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (42197/9765625000000000000 : ℝ)*base90 + (42197/9765625000000000000 : ℝ)*base92 + (42197/9765625000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1041_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1041_box_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2085802553/10000000000 : ℝ)*x 0 + (5377705079/10000000000 : ℝ)*x 1 + (5377704907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2085802553/10000000000 : ℝ)^4117 ≤ (12413803409369/100000000000000 : ℝ)^3093 := by
    have hnat : (2085802553 : ℕ)^4117*100000000000000^3093 ≤ 12413803409369^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085802553 10000000000 12413803409369 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377705079/10000000000 : ℝ)^4117 ≤ (21896549608903/50000000000000 : ℝ)^3093 := by
    have hnat : (5377705079 : ℕ)^4117*50000000000000^3093 ≤ 21896549608903^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377705079 10000000000 21896549608903 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377704907/10000000000 : ℝ)^4117 ≤ (43793097353411/100000000000000 : ℝ)^3093 := by
    have hnat : (5377704907 : ℕ)^4117*100000000000000^3093 ≤ 43793097353411^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377704907 10000000000 43793097353411 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2085802553/10000000000 : ℝ), (5377705079/10000000000 : ℝ), (5377704907/10000000000 : ℝ)] ![(12413803409369/100000000000000 : ℝ), (21896549608903/50000000000000 : ℝ), (43793097353411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2085802553/10000000000 : ℝ)|^4117 ≤ (12413803409369/100000000000000 : ℝ)^3093
        have hw : |(-2085802553/10000000000 : ℝ)|=(2085802553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377705079/10000000000 : ℝ)|^4117 ≤ (21896549608903/50000000000000 : ℝ)^3093
        have hw : |(5377705079/10000000000 : ℝ)|=(5377705079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377704907/10000000000 : ℝ)|^4117 ≤ (43793097353411/100000000000000 : ℝ)^3093
        have hw : |(5377704907/10000000000 : ℝ)|=(5377704907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647456233/5000000000 : ℝ)*x 0 + (-274726579/1250000000 : ℝ)*x 1 + (1075541009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647456233/5000000000 : ℝ)^4117 ≤ (42897962874433/100000000000000 : ℝ)^3093 := by
    have hnat : (2647456233 : ℕ)^4117*100000000000000^3093 ≤ 42897962874433^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647456233 5000000000 42897962874433 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274726579/1250000000 : ℝ)^4117 ≤ (332723456557/2500000000000 : ℝ)^3093 := by
    have hnat : (274726579 : ℕ)^4117*2500000000000^3093 ≤ 332723456557^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274726579 1250000000 332723456557 2500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075541009/2000000000 : ℝ)^4117 ≤ (43793098849263/100000000000000 : ℝ)^3093 := by
    have hnat : (1075541009 : ℕ)^4117*100000000000000^3093 ≤ 43793098849263^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075541009 2000000000 43793098849263 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647456233/5000000000 : ℝ), (-274726579/1250000000 : ℝ), (1075541009/2000000000 : ℝ)] ![(42897962874433/100000000000000 : ℝ), (332723456557/2500000000000 : ℝ), (43793098849263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647456233/5000000000 : ℝ)|^4117 ≤ (42897962874433/100000000000000 : ℝ)^3093
        have hw : |(2647456233/5000000000 : ℝ)|=(2647456233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274726579/1250000000 : ℝ)|^4117 ≤ (332723456557/2500000000000 : ℝ)^3093
        have hw : |(-274726579/1250000000 : ℝ)|=(274726579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075541009/2000000000 : ℝ)|^4117 ≤ (43793098849263/100000000000000 : ℝ)^3093
        have hw : |(1075541009/2000000000 : ℝ)|=(1075541009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294911891/10000000000 : ℝ)*x 0 + (5377705559/10000000000 : ℝ)*x 1 + (-219781271/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294911891/10000000000 : ℝ)^4117 ≤ (2681122292103/6250000000000 : ℝ)^3093 := by
    have hnat : (5294911891 : ℕ)^4117*6250000000000^3093 ≤ 2681122292103^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294911891 10000000000 2681122292103 6250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377705559/10000000000 : ℝ)^4117 ≤ (43793104420771/100000000000000 : ℝ)^3093 := by
    have hnat : (5377705559 : ℕ)^4117*100000000000000^3093 ≤ 43793104420771^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377705559 10000000000 43793104420771 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219781271/1000000000 : ℝ)^4117 ≤ (13308938890987/100000000000000 : ℝ)^3093 := by
    have hnat : (219781271 : ℕ)^4117*100000000000000^3093 ≤ 13308938890987^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219781271 1000000000 13308938890987 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294911891/10000000000 : ℝ), (5377705559/10000000000 : ℝ), (-219781271/1000000000 : ℝ)] ![(2681122292103/6250000000000 : ℝ), (43793104420771/100000000000000 : ℝ), (13308938890987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294911891/10000000000 : ℝ)|^4117 ≤ (2681122292103/6250000000000 : ℝ)^3093
        have hw : |(5294911891/10000000000 : ℝ)|=(5294911891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377705559/10000000000 : ℝ)|^4117 ≤ (43793104420771/100000000000000 : ℝ)^3093
        have hw : |(5377705559/10000000000 : ℝ)|=(5377705559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219781271/1000000000 : ℝ)|^4117 ≤ (13308938890987/100000000000000 : ℝ)^3093
        have hw : |(-219781271/1000000000 : ℝ)|=(219781271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (560972667/1250000000 : ℝ)*x 0 + (2163471169/5000000000 : ℝ)*x 1 + (4326941861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560972667/1250000000 : ℝ)^4117 ≤ (17210748893461/50000000000000 : ℝ)^3093 := by
    have hnat : (560972667 : ℕ)^4117*50000000000000^3093 ≤ 17210748893461^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560972667 1250000000 17210748893461 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163471169/5000000000 : ℝ)^4117 ≤ (8197313375649/25000000000000 : ℝ)^3093 := by
    have hnat : (2163471169 : ℕ)^4117*25000000000000^3093 ≤ 8197313375649^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163471169 5000000000 8197313375649 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326941861/10000000000 : ℝ)^4117 ≤ (6557849738243/20000000000000 : ℝ)^3093 := by
    have hnat : (4326941861 : ℕ)^4117*20000000000000^3093 ≤ 6557849738243^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326941861 10000000000 6557849738243 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(560972667/1250000000 : ℝ), (2163471169/5000000000 : ℝ), (4326941861/10000000000 : ℝ)] ![(17210748893461/50000000000000 : ℝ), (8197313375649/25000000000000 : ℝ), (6557849738243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(560972667/1250000000 : ℝ)|^4117 ≤ (17210748893461/50000000000000 : ℝ)^3093
        have hw : |(560972667/1250000000 : ℝ)|=(560972667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2163471169/5000000000 : ℝ)|^4117 ≤ (8197313375649/25000000000000 : ℝ)^3093
        have hw : |(2163471169/5000000000 : ℝ)|=(2163471169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326941861/10000000000 : ℝ)|^4117 ≤ (6557849738243/20000000000000 : ℝ)^3093
        have hw : |(4326941861/10000000000 : ℝ)|=(4326941861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2347862669/10000000000 : ℝ)*x 0 + (2639853917/5000000000 : ℝ)*x 1 + (659963377/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2347862669/10000000000 : ℝ)^4117 ≤ (14531859777851/100000000000000 : ℝ)^3093 := by
    have hnat : (2347862669 : ℕ)^4117*100000000000000^3093 ≤ 14531859777851^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347862669 10000000000 14531859777851 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639853917/5000000000 : ℝ)^4117 ≤ (667719914201/1562500000000 : ℝ)^3093 := by
    have hnat : (2639853917 : ℕ)^4117*1562500000000^3093 ≤ 667719914201^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639853917 5000000000 667719914201 1562500000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659963377/1250000000 : ℝ)^4117 ≤ (42734065695967/100000000000000 : ℝ)^3093 := by
    have hnat : (659963377 : ℕ)^4117*100000000000000^3093 ≤ 42734065695967^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659963377 1250000000 42734065695967 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2347862669/10000000000 : ℝ), (2639853917/5000000000 : ℝ), (659963377/1250000000 : ℝ)] ![(14531859777851/100000000000000 : ℝ), (667719914201/1562500000000 : ℝ), (42734065695967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2347862669/10000000000 : ℝ)|^4117 ≤ (14531859777851/100000000000000 : ℝ)^3093
        have hw : |(-2347862669/10000000000 : ℝ)|=(2347862669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639853917/5000000000 : ℝ)|^4117 ≤ (667719914201/1562500000000 : ℝ)^3093
        have hw : |(2639853917/5000000000 : ℝ)|=(2639853917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659963377/1250000000 : ℝ)|^4117 ≤ (42734065695967/100000000000000 : ℝ)^3093
        have hw : |(659963377/1250000000 : ℝ)|=(659963377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072861391/2000000000 : ℝ)*x 0 + (-559011661/2500000000 : ℝ)*x 1 + (2639853627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072861391/2000000000 : ℝ)^4117 ≤ (5455991256027/12500000000000 : ℝ)^3093 := by
    have hnat : (1072861391 : ℕ)^4117*12500000000000^3093 ≤ 5455991256027^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072861391 2000000000 5455991256027 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559011661/2500000000 : ℝ)^4117 ≤ (13618001683761/100000000000000 : ℝ)^3093 := by
    have hnat : (559011661 : ℕ)^4117*100000000000000^3093 ≤ 13618001683761^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559011661 2500000000 13618001683761 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2639853627/5000000000 : ℝ)^4117 ≤ (42734068260111/100000000000000 : ℝ)^3093 := by
    have hnat : (2639853627 : ℕ)^4117*100000000000000^3093 ≤ 42734068260111^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639853627 5000000000 42734068260111 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072861391/2000000000 : ℝ), (-559011661/2500000000 : ℝ), (2639853627/5000000000 : ℝ)] ![(5455991256027/12500000000000 : ℝ), (13618001683761/100000000000000 : ℝ), (42734068260111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072861391/2000000000 : ℝ)|^4117 ≤ (5455991256027/12500000000000 : ℝ)^3093
        have hw : |(1072861391/2000000000 : ℝ)|=(1072861391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-559011661/2500000000 : ℝ)|^4117 ≤ (13618001683761/100000000000000 : ℝ)^3093
        have hw : |(-559011661/2500000000 : ℝ)|=(559011661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2639853627/5000000000 : ℝ)|^4117 ≤ (42734068260111/100000000000000 : ℝ)^3093
        have hw : |(2639853627/5000000000 : ℝ)|=(2639853627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364306439/10000000000 : ℝ)*x 0 + (1319926883/2500000000 : ℝ)*x 1 + (-2236046963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364306439/10000000000 : ℝ)^4117 ≤ (43647924459647/100000000000000 : ℝ)^3093 := by
    have hnat : (5364306439 : ℕ)^4117*100000000000000^3093 ≤ 43647924459647^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364306439 10000000000 43647924459647 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319926883/2500000000 : ℝ)^4117 ≤ (42734071255203/100000000000000 : ℝ)^3093 := by
    have hnat : (1319926883 : ℕ)^4117*100000000000000^3093 ≤ 42734071255203^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319926883 2500000000 42734071255203 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236046963/10000000000 : ℝ)^4117 ≤ (2723600853947/20000000000000 : ℝ)^3093 := by
    have hnat : (2236046963 : ℕ)^4117*20000000000000^3093 ≤ 2723600853947^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236046963 10000000000 2723600853947 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364306439/10000000000 : ℝ), (1319926883/2500000000 : ℝ), (-2236046963/10000000000 : ℝ)] ![(43647924459647/100000000000000 : ℝ), (42734071255203/100000000000000 : ℝ), (2723600853947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364306439/10000000000 : ℝ)|^4117 ≤ (43647924459647/100000000000000 : ℝ)^3093
        have hw : |(5364306439/10000000000 : ℝ)|=(5364306439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319926883/2500000000 : ℝ)|^4117 ≤ (42734071255203/100000000000000 : ℝ)^3093
        have hw : |(1319926883/2500000000 : ℝ)|=(1319926883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236046963/10000000000 : ℝ)|^4117 ≤ (2723600853947/20000000000000 : ℝ)^3093
        have hw : |(-2236046963/10000000000 : ℝ)|=(2236046963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213505139/500000000 : ℝ)*x 0 + (2217880021/5000000000 : ℝ)*x 1 + (3465437/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213505139/500000000 : ℝ)^4117 ≤ (64434354629/200000000000 : ℝ)^3093 := by
    have hnat : (213505139 : ℕ)^4117*200000000000^3093 ≤ 64434354629^3093*500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213505139 500000000 64434354629 200000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217880021/5000000000 : ℝ)^4117 ≤ (8472853701293/25000000000000 : ℝ)^3093 := by
    have hnat : (2217880021 : ℕ)^4117*25000000000000^3093 ≤ 8472853701293^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217880021 5000000000 8472853701293 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3465437/7812500 : ℝ)^4117 ≤ (6778281573841/20000000000000 : ℝ)^3093 := by
    have hnat : (3465437 : ℕ)^4117*20000000000000^3093 ≤ 6778281573841^3093*7812500^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3465437 7812500 6778281573841 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213505139/500000000 : ℝ), (2217880021/5000000000 : ℝ), (3465437/7812500 : ℝ)] ![(64434354629/200000000000 : ℝ), (8472853701293/25000000000000 : ℝ), (6778281573841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213505139/500000000 : ℝ)|^4117 ≤ (64434354629/200000000000 : ℝ)^3093
        have hw : |(213505139/500000000 : ℝ)|=(213505139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217880021/5000000000 : ℝ)|^4117 ≤ (8472853701293/25000000000000 : ℝ)^3093
        have hw : |(2217880021/5000000000 : ℝ)|=(2217880021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3465437/7812500 : ℝ)|^4117 ≤ (6778281573841/20000000000000 : ℝ)^3093
        have hw : |(3465437/7812500 : ℝ)|=(3465437/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_8 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1146593699/5000000000 : ℝ)*x 0 + (5213259653/10000000000 : ℝ)*x 1 + (673412817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1146593699/5000000000 : ℝ)^4117 ≤ (3520790425187/25000000000000 : ℝ)^3093 := by
    have hnat : (1146593699 : ℕ)^4117*25000000000000^3093 ≤ 3520790425187^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146593699 5000000000 3520790425187 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213259653/10000000000 : ℝ)^4117 ≤ (10504919153951/25000000000000 : ℝ)^3093 := by
    have hnat : (5213259653 : ℕ)^4117*25000000000000^3093 ≤ 10504919153951^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213259653 10000000000 10504919153951 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673412817/1250000000 : ℝ)^4117 ≤ (5487145208699/12500000000000 : ℝ)^3093 := by
    have hnat : (673412817 : ℕ)^4117*12500000000000^3093 ≤ 5487145208699^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673412817 1250000000 5487145208699 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1146593699/5000000000 : ℝ), (5213259653/10000000000 : ℝ), (673412817/1250000000 : ℝ)] ![(3520790425187/25000000000000 : ℝ), (10504919153951/25000000000000 : ℝ), (5487145208699/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1146593699/5000000000 : ℝ)|^4117 ≤ (3520790425187/25000000000000 : ℝ)^3093
        have hw : |(-1146593699/5000000000 : ℝ)|=(1146593699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213259653/10000000000 : ℝ)|^4117 ≤ (10504919153951/25000000000000 : ℝ)^3093
        have hw : |(5213259653/10000000000 : ℝ)|=(5213259653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673412817/1250000000 : ℝ)|^4117 ≤ (5487145208699/12500000000000 : ℝ)^3093
        have hw : |(673412817/1250000000 : ℝ)|=(673412817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_9 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528811207/1000000000 : ℝ)*x 0 + (-1096998833/5000000000 : ℝ)*x 1 + (107746047/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528811207/1000000000 : ℝ)^4117 ≤ (42824643176571/100000000000000 : ℝ)^3093 := by
    have hnat : (528811207 : ℕ)^4117*100000000000000^3093 ≤ 42824643176571^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528811207 1000000000 42824643176571 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096998833/5000000000 : ℝ)^4117 ≤ (13278197154803/100000000000000 : ℝ)^3093 := by
    have hnat : (1096998833 : ℕ)^4117*100000000000000^3093 ≤ 13278197154803^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096998833 5000000000 13278197154803 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107746047/200000000 : ℝ)^4117 ≤ (43897159652253/100000000000000 : ℝ)^3093 := by
    have hnat : (107746047 : ℕ)^4117*100000000000000^3093 ≤ 43897159652253^3093*200000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107746047 200000000 43897159652253 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528811207/1000000000 : ℝ), (-1096998833/5000000000 : ℝ), (107746047/200000000 : ℝ)] ![(42824643176571/100000000000000 : ℝ), (13278197154803/100000000000000 : ℝ), (43897159652253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528811207/1000000000 : ℝ)|^4117 ≤ (42824643176571/100000000000000 : ℝ)^3093
        have hw : |(528811207/1000000000 : ℝ)|=(528811207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096998833/5000000000 : ℝ)|^4117 ≤ (13278197154803/100000000000000 : ℝ)^3093
        have hw : |(-1096998833/5000000000 : ℝ)|=(1096998833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107746047/200000000 : ℝ)|^4117 ≤ (43897159652253/100000000000000 : ℝ)^3093
        have hw : |(107746047/200000000 : ℝ)|=(107746047/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_10 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288112369/10000000000 : ℝ)*x 0 + (269365123/500000000 : ℝ)*x 1 + (-1096998559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288112369/10000000000 : ℝ)^4117 ≤ (5353080799951/12500000000000 : ℝ)^3093 := by
    have hnat : (5288112369 : ℕ)^4117*12500000000000^3093 ≤ 5353080799951^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288112369 10000000000 5353080799951 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269365123/500000000 : ℝ)^4117 ≤ (43897160845303/100000000000000 : ℝ)^3093 := by
    have hnat : (269365123 : ℕ)^4117*100000000000000^3093 ≤ 43897160845303^3093*500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269365123 500000000 43897160845303 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096998559/5000000000 : ℝ)^4117 ≤ (13278192740273/100000000000000 : ℝ)^3093 := by
    have hnat : (1096998559 : ℕ)^4117*100000000000000^3093 ≤ 13278192740273^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096998559 5000000000 13278192740273 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288112369/10000000000 : ℝ), (269365123/500000000 : ℝ), (-1096998559/5000000000 : ℝ)] ![(5353080799951/12500000000000 : ℝ), (43897160845303/100000000000000 : ℝ), (13278192740273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288112369/10000000000 : ℝ)|^4117 ≤ (5353080799951/12500000000000 : ℝ)^3093
        have hw : |(5288112369/10000000000 : ℝ)|=(5288112369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269365123/500000000 : ℝ)|^4117 ≤ (43897160845303/100000000000000 : ℝ)^3093
        have hw : |(269365123/500000000 : ℝ)|=(269365123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1096998559/5000000000 : ℝ)|^4117 ≤ (13278192740273/100000000000000 : ℝ)^3093
        have hw : |(-1096998559/5000000000 : ℝ)|=(1096998559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_11 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2254412871/5000000000 : ℝ)*x 0 + (4316279247/10000000000 : ℝ)*x 1 + (4316279499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254412871/5000000000 : ℝ)^4117 ≤ (34636514554347/100000000000000 : ℝ)^3093 := by
    have hnat : (2254412871 : ℕ)^4117*100000000000000^3093 ≤ 34636514554347^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254412871 5000000000 34636514554347 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316279247/10000000000 : ℝ)^4117 ≤ (3268174144187/10000000000000 : ℝ)^3093 := by
    have hnat : (4316279247 : ℕ)^4117*10000000000000^3093 ≤ 3268174144187^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316279247 10000000000 3268174144187 10000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316279499/10000000000 : ℝ)^4117 ≤ (4085217997707/12500000000000 : ℝ)^3093 := by
    have hnat : (4316279499 : ℕ)^4117*12500000000000^3093 ≤ 4085217997707^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316279499 10000000000 4085217997707 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2254412871/5000000000 : ℝ), (4316279247/10000000000 : ℝ), (4316279499/10000000000 : ℝ)] ![(34636514554347/100000000000000 : ℝ), (3268174144187/10000000000000 : ℝ), (4085217997707/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2254412871/5000000000 : ℝ)|^4117 ≤ (34636514554347/100000000000000 : ℝ)^3093
        have hw : |(2254412871/5000000000 : ℝ)|=(2254412871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316279247/10000000000 : ℝ)|^4117 ≤ (3268174144187/10000000000000 : ℝ)^3093
        have hw : |(4316279247/10000000000 : ℝ)|=(4316279247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316279499/10000000000 : ℝ)|^4117 ≤ (4085217997707/12500000000000 : ℝ)^3093
        have hw : |(4316279499/10000000000 : ℝ)|=(4316279499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_12 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-535215763/2500000000 : ℝ)*x 0 + (1360699291/2500000000 : ℝ)*x 1 + (32948251/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535215763/2500000000 : ℝ)^4117 ≤ (12851885383283/100000000000000 : ℝ)^3093 := by
    have hnat : (535215763 : ℕ)^4117*100000000000000^3093 ≤ 12851885383283^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535215763 2500000000 12851885383283 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360699291/2500000000 : ℝ)^4117 ≤ (22250037713999/50000000000000 : ℝ)^3093 := by
    have hnat : (1360699291 : ℕ)^4117*50000000000000^3093 ≤ 22250037713999^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360699291 2500000000 22250037713999 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32948251/62500000 : ℝ)^4117 ≤ (42648039169329/100000000000000 : ℝ)^3093 := by
    have hnat : (32948251 : ℕ)^4117*100000000000000^3093 ≤ 42648039169329^3093*62500000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32948251 62500000 42648039169329 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535215763/2500000000 : ℝ), (1360699291/2500000000 : ℝ), (32948251/62500000 : ℝ)] ![(12851885383283/100000000000000 : ℝ), (22250037713999/50000000000000 : ℝ), (42648039169329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535215763/2500000000 : ℝ)|^4117 ≤ (12851885383283/100000000000000 : ℝ)^3093
        have hw : |(-535215763/2500000000 : ℝ)|=(535215763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360699291/2500000000 : ℝ)|^4117 ≤ (22250037713999/50000000000000 : ℝ)^3093
        have hw : |(1360699291/2500000000 : ℝ)|=(1360699291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32948251/62500000 : ℝ)|^4117 ≤ (42648039169329/100000000000000 : ℝ)^3093
        have hw : |(32948251/62500000 : ℝ)|=(32948251/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_13 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369960733/10000000000 : ℝ)*x 0 + (-1119551833/5000000000 : ℝ)*x 1 + (5271719923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369960733/10000000000 : ℝ)^4117 ≤ (10927293580039/25000000000000 : ℝ)^3093 := by
    have hnat : (5369960733 : ℕ)^4117*25000000000000^3093 ≤ 10927293580039^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369960733 10000000000 10927293580039 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119551833/5000000000 : ℝ)^4117 ≤ (852674315259/6250000000000 : ℝ)^3093 := by
    have hnat : (1119551833 : ℕ)^4117*6250000000000^3093 ≤ 852674315259^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119551833 5000000000 852674315259 6250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271719923/10000000000 : ℝ)^4117 ≤ (42648036617239/100000000000000 : ℝ)^3093 := by
    have hnat : (5271719923 : ℕ)^4117*100000000000000^3093 ≤ 42648036617239^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271719923 10000000000 42648036617239 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369960733/10000000000 : ℝ), (-1119551833/5000000000 : ℝ), (5271719923/10000000000 : ℝ)] ![(10927293580039/25000000000000 : ℝ), (852674315259/6250000000000 : ℝ), (42648036617239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369960733/10000000000 : ℝ)|^4117 ≤ (10927293580039/25000000000000 : ℝ)^3093
        have hw : |(5369960733/10000000000 : ℝ)|=(5369960733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119551833/5000000000 : ℝ)|^4117 ≤ (852674315259/6250000000000 : ℝ)^3093
        have hw : |(-1119551833/5000000000 : ℝ)|=(1119551833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271719923/10000000000 : ℝ)|^4117 ≤ (42648036617239/100000000000000 : ℝ)^3093
        have hw : |(5271719923/10000000000 : ℝ)|=(5271719923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_14 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342490293/2500000000 : ℝ)*x 0 + (5271719229/10000000000 : ℝ)*x 1 + (-2239104001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342490293/2500000000 : ℝ)^4117 ≤ (43709179076431/100000000000000 : ℝ)^3093 := by
    have hnat : (1342490293 : ℕ)^4117*100000000000000^3093 ≤ 43709179076431^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342490293 2500000000 43709179076431 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271719229/10000000000 : ℝ)^4117 ≤ (4264802914403/10000000000000 : ℝ)^3093 := by
    have hnat : (5271719229 : ℕ)^4117*10000000000000^3093 ≤ 4264802914403^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271719229 10000000000 4264802914403 10000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239104001/10000000000 : ℝ)^4117 ≤ (13642791761051/100000000000000 : ℝ)^3093 := by
    have hnat : (2239104001 : ℕ)^4117*100000000000000^3093 ≤ 13642791761051^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239104001 10000000000 13642791761051 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342490293/2500000000 : ℝ), (5271719229/10000000000 : ℝ), (-2239104001/10000000000 : ℝ)] ![(43709179076431/100000000000000 : ℝ), (4264802914403/10000000000000 : ℝ), (13642791761051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342490293/2500000000 : ℝ)|^4117 ≤ (43709179076431/100000000000000 : ℝ)^3093
        have hw : |(1342490293/2500000000 : ℝ)|=(1342490293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271719229/10000000000 : ℝ)|^4117 ≤ (4264802914403/10000000000000 : ℝ)^3093
        have hw : |(5271719229/10000000000 : ℝ)|=(5271719229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239104001/10000000000 : ℝ)|^4117 ≤ (13642791761051/100000000000000 : ℝ)^3093
        have hw : |(-2239104001/10000000000 : ℝ)|=(2239104001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_box_15 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126065857/5000000000 : ℝ)*x 0 + (69447233/156250000 : ℝ)*x 1 + (4444624289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126065857/5000000000 : ℝ)^4117 ≤ (640736506013/2000000000000 : ℝ)^3093 := by
    have hnat : (2126065857 : ℕ)^4117*2000000000000^3093 ≤ 640736506013^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126065857 5000000000 640736506013 2000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69447233/156250000 : ℝ)^4117 ≤ (16990790167057/50000000000000 : ℝ)^3093 := by
    have hnat : (69447233 : ℕ)^4117*50000000000000^3093 ≤ 16990790167057^3093*156250000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69447233 156250000 16990790167057 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4444624289/10000000000 : ℝ)^4117 ≤ (8495398586879/25000000000000 : ℝ)^3093 := by
    have hnat : (4444624289 : ℕ)^4117*25000000000000^3093 ≤ 8495398586879^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444624289 10000000000 8495398586879 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126065857/5000000000 : ℝ), (69447233/156250000 : ℝ), (4444624289/10000000000 : ℝ)] ![(640736506013/2000000000000 : ℝ), (16990790167057/50000000000000 : ℝ), (8495398586879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126065857/5000000000 : ℝ)|^4117 ≤ (640736506013/2000000000000 : ℝ)^3093
        have hw : |(2126065857/5000000000 : ℝ)|=(2126065857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(69447233/156250000 : ℝ)|^4117 ≤ (16990790167057/50000000000000 : ℝ)^3093
        have hw : |(69447233/156250000 : ℝ)|=(69447233/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4444624289/10000000000 : ℝ)|^4117 ≤ (8495398586879/25000000000000 : ℝ)^3093
        have hw : |(4444624289/10000000000 : ℝ)|=(4444624289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29611/50000 : ℝ) ∧ (79493/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16579/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11217/100000 : ℝ) ^ (8233/2048 : ℝ) ≤ (3030510914393781/20000000000000000000 : ℝ) := by
    have hpowers : (11217/100000 : ℝ)^8233 ≤ (3030510914393781/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11217 : ℕ)^8233*20000000000000000000^2048 ≤ 3030510914393781^2048*100000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11217 100000 3030510914393781 20000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11217/100000 : ℝ)) (X := (3030510914393781/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13987/100000 : ℝ) ^ (8233/2048 : ℝ) ≤ (18397809188367643/50000000000000000000 : ℝ) := by
    have hpowers : (13987/100000 : ℝ)^8233 ≤ (18397809188367643/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13987 : ℕ)^8233*50000000000000000000^2048 ≤ 18397809188367643^2048*100000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13987 100000 18397809188367643 50000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13987/100000 : ℝ)) (X := (18397809188367643/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003030510914393781/10000000000000000000 : ℝ) ≤ (10000753768975571/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (10003030510914393781/10000000000000000000 : ℝ)^2048 ≤ (10000753768975571/10000000000000000 : ℝ)^8233 := by
      have hnat : (10003030510914393781 : ℕ)^2048*10000000000000000^8233 ≤ 10000753768975571^8233*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003030510914393781 10000000000000000000 10000753768975571 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000753768975571/10000000000000000 : ℝ)) (X := (10003030510914393781/10000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051948172948704191/100000000000000000000 : ℝ) ≤ (5000645992376673/5000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (100051948172948704191/100000000000000000000 : ℝ)^2048 ≤ (5000645992376673/5000000000000000 : ℝ)^8233 := by
      have hnat : (100051948172948704191 : ℕ)^2048*5000000000000000^8233 ≤ 5000645992376673^8233*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051948172948704191 100000000000000000000 5000645992376673 5000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000645992376673/5000000000000000 : ℝ)) (X := (100051948172948704191/100000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018397809188367643/25000000000000000000 : ℝ) ≤ (10001830200531121/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (25018397809188367643/25000000000000000000 : ℝ)^2048 ≤ (10001830200531121/10000000000000000 : ℝ)^8233 := by
      have hnat : (25018397809188367643 : ℕ)^2048*10000000000000000^8233 ≤ 10001830200531121^8233*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018397809188367643 25000000000000000000 10001830200531121 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001830200531121/10000000000000000 : ℝ)) (X := (25018397809188367643/25000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3030510914393781/20000000000000000000 : ℝ) ≤ ((692250340182593183/692500000000000000 : ℝ)+2*(21528631111/11080000000000 : ℝ)*(11217/100000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (692250340182593183/692500000000000000 : ℝ)+2*(21528631111/11080000000000 : ℝ)*(11217/100000 : ℝ)=(10000753768975571/10000000000000000 : ℝ) by norm_num, show 1+2*(3030510914393781/20000000000000000000 : ℝ)=(10003030510914393781/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18397809188367643/50000000000000000000 : ℝ)+(3030510914393781/20000000000000000000 : ℝ) ≤ ((692250340182593183/692500000000000000 : ℝ)+(21528631111/11080000000000 : ℝ)*((13987/100000 : ℝ)+(11217/100000 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (692250340182593183/692500000000000000 : ℝ)+(21528631111/11080000000000 : ℝ)*((13987/100000 : ℝ)+(11217/100000 : ℝ))=(5000645992376673/5000000000000000 : ℝ) by norm_num, show 1+(18397809188367643/50000000000000000000 : ℝ)+(3030510914393781/20000000000000000000 : ℝ)=(100051948172948704191/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18397809188367643/50000000000000000000 : ℝ) ≤ ((692250340182593183/692500000000000000 : ℝ)+2*(21528631111/11080000000000 : ℝ)*(13987/100000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (692250340182593183/692500000000000000 : ℝ)+2*(21528631111/11080000000000 : ℝ)*(13987/100000 : ℝ)=(10001830200531121/10000000000000000 : ℝ) by norm_num, show 1+2*(18397809188367643/50000000000000000000 : ℝ)=(25018397809188367643/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (692250340182593183/692500000000000000 : ℝ)*(X 1 0+X 2 0)+(21528631111/11080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (692250340182593183/692500000000000000 : ℝ)) (alpha := (21528631111/11080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (692250340182593183/692500000000000000 : ℝ)*(X 0 1+X 2 1)+(21528631111/11080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (692250340182593183/692500000000000000 : ℝ)) (alpha := (21528631111/11080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (692250340182593183/692500000000000000 : ℝ)*(X 0 2+X 1 2)+(21528631111/11080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (692250340182593183/692500000000000000 : ℝ)) (alpha := (21528631111/11080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2085802553/10000000000 : ℝ)*X 0 0+(5377705079/10000000000 : ℝ)*X 0 1+(5377704907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647456233/5000000000 : ℝ)*X 1 0+(-274726579/1250000000 : ℝ)*X 1 1+(1075541009/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294911891/10000000000 : ℝ)*X 2 0+(5377705559/10000000000 : ℝ)*X 2 1+(-219781271/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((560972667/1250000000 : ℝ)*X 0 0+(2163471169/5000000000 : ℝ)*X 0 1+(4326941861/10000000000 : ℝ)*X 0 2+(560972667/1250000000 : ℝ)*X 1 0+(2163471169/5000000000 : ℝ)*X 1 1+(4326941861/10000000000 : ℝ)*X 1 2+(560972667/1250000000 : ℝ)*X 2 0+(2163471169/5000000000 : ℝ)*X 2 1+(4326941861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2347862669/10000000000 : ℝ)*X 0 0+(2639853917/5000000000 : ℝ)*X 0 1+(659963377/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072861391/2000000000 : ℝ)*X 1 0+(-559011661/2500000000 : ℝ)*X 1 1+(2639853627/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364306439/10000000000 : ℝ)*X 2 0+(1319926883/2500000000 : ℝ)*X 2 1+(-2236046963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((213505139/500000000 : ℝ)*X 0 0+(2217880021/5000000000 : ℝ)*X 0 1+(3465437/7812500 : ℝ)*X 0 2+(213505139/500000000 : ℝ)*X 1 0+(2217880021/5000000000 : ℝ)*X 1 1+(3465437/7812500 : ℝ)*X 1 2+(213505139/500000000 : ℝ)*X 2 0+(2217880021/5000000000 : ℝ)*X 2 1+(3465437/7812500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1146593699/5000000000 : ℝ)*X 0 0+(5213259653/10000000000 : ℝ)*X 0 1+(673412817/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((528811207/1000000000 : ℝ)*X 1 0+(-1096998833/5000000000 : ℝ)*X 1 1+(107746047/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288112369/10000000000 : ℝ)*X 2 0+(269365123/500000000 : ℝ)*X 2 1+(-1096998559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2254412871/5000000000 : ℝ)*X 0 0+(4316279247/10000000000 : ℝ)*X 0 1+(4316279499/10000000000 : ℝ)*X 0 2+(2254412871/5000000000 : ℝ)*X 1 0+(4316279247/10000000000 : ℝ)*X 1 1+(4316279499/10000000000 : ℝ)*X 1 2+(2254412871/5000000000 : ℝ)*X 2 0+(4316279247/10000000000 : ℝ)*X 2 1+(4316279499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-535215763/2500000000 : ℝ)*X 0 0+(1360699291/2500000000 : ℝ)*X 0 1+(32948251/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369960733/10000000000 : ℝ)*X 1 0+(-1119551833/5000000000 : ℝ)*X 1 1+(5271719923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342490293/2500000000 : ℝ)*X 2 0+(5271719229/10000000000 : ℝ)*X 2 1+(-2239104001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2126065857/5000000000 : ℝ)*X 0 0+(69447233/156250000 : ℝ)*X 0 1+(4444624289/10000000000 : ℝ)*X 0 2+(2126065857/5000000000 : ℝ)*X 1 0+(69447233/156250000 : ℝ)*X 1 1+(4444624289/10000000000 : ℝ)*X 1 2+(2126065857/5000000000 : ℝ)*X 2 0+(69447233/156250000 : ℝ)*X 2 1+(4444624289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-10772008040306650870848112067919/17312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14128403/25000000000000 : ℝ)*(upper0) + (102494311/20000000000000 : ℝ)*(upper3) + (2588321/5000000000000 : ℝ)*(lower4) + (3835298454578119/100000000000000 : ℝ)*(major0) + (3835298454578119/100000000000000 : ℝ)*(major1) + (3835298454578119/100000000000000 : ℝ)*(major2) + (40171181433/100000000000000 : ℝ)*(sp1) + (9773592497/100000000000000 : ℝ)*(sp2) + (27208680933/100000000000000 : ℝ)*(sp3) + (636407135214751/12500000000000 : ℝ)*(sp4) + (318201070669987/6250000000000 : ℝ)*(sp5) + (636405941038591/12500000000000 : ℝ)*(sp6) + (1300026363465429/50000000000000 : ℝ)*(sp7) + (220183217/100000000000000 : ℝ)*(sp8) + (260007993561179/10000000000000 : ℝ)*(f.failure) + (203650292076049/4000000000000 : ℝ)*(f.sum) + (1640348068669/554000000000000000000000000 : ℝ)*base65 + (914690913154324723/69250000000000000000000000000000 : ℝ)*base68 + (777189073651824723/69250000000000000000000000000000 : ℝ)*base70 + (560879720537074723/69250000000000000000000000000000 : ℝ)*base72 + (1584412475567/110800000000000000000000000 : ℝ)*base74 + (944657609902074723/69250000000000000000000000000000 : ℝ)*base76 + (1019507531996324723/69250000000000000000000000000000 : ℝ)*base78 + (1128861923435175277/69250000000000000000000000000000 : ℝ)*base79 + (1092106381277/554000000000000000000000000 : ℝ)*base82 + (10367/7812500000000000000 : ℝ)*base89 + (10367/7812500000000000000 : ℝ)*base91 + (10367/7812500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29611/50000 : ℝ) ≤ (5126636215423130507848791/8656250000000000000000000 : ℝ) := by norm_num
    linear_combination (9070173/10000000000000 : ℝ)*(lower0) + (109103379/100000000000000 : ℝ)*(upper2) + (44158959/100000000000000 : ℝ)*(upper3) + (133741541/100000000000000 : ℝ)*(lower5) + (121805884016777/3125000000000 : ℝ)*(major0) + (121805884016777/3125000000000 : ℝ)*(major1) + (121805884016777/3125000000000 : ℝ)*(major2) + (5133391087314423/100000000000000 : ℝ)*(sp0) + (2566694182308269/50000000000000 : ℝ)*(sp1) + (641670193970251/12500000000000 : ℝ)*(sp2) + (1321217348235699/50000000000000 : ℝ)*(sp3) + (544539577/20000000000000 : ℝ)*(sp5) + (14767776207/50000000000000 : ℝ)*(sp6) + (4616927129/50000000000000 : ℝ)*(sp7) + (330305491290707/12500000000000 : ℝ)*(f.failure) + (5133391087314423/100000000000000 : ℝ)*(f.sum) + (173069563379/277000000000000000000000000 : ℝ)*base65 + (12525018677959257/4328125000000000000000000000000 : ℝ)*base67 + (4686888953821993/4328125000000000000000000000000 : ℝ)*base70 + (24707486517321993/4328125000000000000000000000000 : ℝ)*base72 + (1963444662261/69250000000000000000000000 : ℝ)*base73 + (192189690661037/67626953125000000000000000000 : ℝ)*base76 + (3812248278845283/1082031250000000000000000000000 : ℝ)*base77 + (85021117980143691/2164062500000000000000000000000 : ℝ)*base79 + (20008586417/13850000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (20193/4882812500000000000 : ℝ)*base89 + (20193/4882812500000000000 : ℝ)*base91 + (20193/4882812500000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79493/100000 : ℝ) ≤ (3440669300427770288179501549029/4328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21436827/12500000000000 : ℝ)*(upper0) + (65114547/50000000000000 : ℝ)*(lower3) + (82024769/25000000000000 : ℝ)*(upper4) + (1091516016584021/25000000000000 : ℝ)*(major0) + (1091516016584021/25000000000000 : ℝ)*(major1) + (1091516016584021/25000000000000 : ℝ)*(major2) + (119084597347/100000000000000 : ℝ)*(sp1) + (10905367899/3125000000000 : ℝ)*(sp2) + (59020421907/50000000000000 : ℝ)*(sp3) + (4225571897/50000000000000 : ℝ)*(sp4) + (718214632107517/12500000000000 : ℝ)*(sp8) + (5745606423406583/100000000000000 : ℝ)*(sp9) + (5745376536231161/100000000000000 : ℝ)*(sp10) + (1479893023847983/50000000000000 : ℝ)*(sp11) + (147995204426989/5000000000000 : ℝ)*(f.failure) + (574572550800393/10000000000000 : ℝ)*(f.sum) + (234919943703/69250000000000000000000000 : ℝ)*base66 + (250480420324608657/17312500000000000000000000000000 : ℝ)*base68 + (10831667308983657/17312500000000000000000000000000 : ℝ)*base70 + (303172867377733657/17312500000000000000000000000000 : ℝ)*base72 + (5393021314279/138500000000000000000000000 : ℝ)*base73 + (98781280559296157/17312500000000000000000000000000 : ℝ)*base76 + (103385408705546157/17312500000000000000000000000000 : ℝ)*base78 + (233798707929391343/17312500000000000000000000000000 : ℝ)*base79 + (400358446327/69250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2907/976562500000000000 : ℝ)*base90 + (2907/976562500000000000 : ℝ)*base92 + (2907/976562500000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-16579/20000 : ℝ) ≤ (-2870160922900952772798676989633/3462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65872971/100000000000000 : ℝ)*(lower1) + (39241571/20000000000000 : ℝ)*(lower3) + (256700353/100000000000000 : ℝ)*(lower4) + (28798871/12500000000000 : ℝ)*(upper5) + (440045237647717/10000000000000 : ℝ)*(major0) + (440045237647717/10000000000000 : ℝ)*(major1) + (440045237647717/10000000000000 : ℝ)*(major2) + (2566303351/25000000000000 : ℝ)*(sp5) + (918016042927/100000000000000 : ℝ)*(sp6) + (467423961/5000000000000 : ℝ)*(sp7) + (1461329641196317/25000000000000 : ℝ)*(sp12) + (730663537446483/12500000000000 : ℝ)*(sp13) + (292220027437117/5000000000000 : ℝ)*(sp14) + (745801937775411/25000000000000 : ℝ)*(sp15) + (596643419916173/20000000000000 : ℝ)*(f.failure) + (1461329641196317/25000000000000 : ℝ)*(f.sum) + (91520574319/11080000000000000000000000 : ℝ)*base65 + (9845027252900711/6925000000000000000000000000000 : ℝ)*base67 + (74060756578399289/6925000000000000000000000000000 : ℝ)*base70 + (16884732759000711/6925000000000000000000000000000 : ℝ)*base71 + (1615825801799/277000000000000000000000000 : ℝ)*base73 + (55981494318799289/6925000000000000000000000000000 : ℝ)*base76 + (18194331274575711/6925000000000000000000000000000 : ℝ)*base77 + (29773085404300711/6925000000000000000000000000000 : ℝ)*base79 + (142422208069/6925000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (60177/7812500000000000000 : ℝ)*base89 + (60177/7812500000000000000 : ℝ)*base91 + (60177/7812500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1041_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29611/50000 : ℝ) else (79493/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16579/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1041_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1041_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29611/50000 : ℝ) else (79493/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16579/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1041_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1041_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29611/50000 : ℝ) else (79493/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16579/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1041_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
