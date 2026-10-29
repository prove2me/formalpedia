-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1424_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:16.045108+00:00
-- url     : https://prove2.me/submissions/8a2f8a9d-c0d9-44b3-ab8a-05d90f39a986

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
theorem support_rectangle_w1424_s6_0 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-987597139/5000000000 : ℝ)*x 0 + (5408478551/10000000000 : ℝ)*x 1 + (1311697993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987597139/5000000000 : ℝ)^137 ≤ (3012163448129/25000000000000 : ℝ)^105 := by
    have hnat : (987597139 : ℕ)^137*25000000000000^105 ≤ 3012163448129^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987597139 5000000000 3012163448129 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408478551/10000000000 : ℝ)^137 ≤ (22423147754993/50000000000000 : ℝ)^105 := by
    have hnat : (5408478551 : ℕ)^137*50000000000000^105 ≤ 22423147754993^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408478551 10000000000 22423147754993 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311697993/2500000000 : ℝ)^137 ≤ (172420202761/400000000000 : ℝ)^105 := by
    have hnat : (1311697993 : ℕ)^137*400000000000^105 ≤ 172420202761^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311697993 2500000000 172420202761 400000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987597139/5000000000 : ℝ), (5408478551/10000000000 : ℝ), (1311697993/2500000000 : ℝ)] ![(3012163448129/25000000000000 : ℝ), (22423147754993/50000000000000 : ℝ), (172420202761/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987597139/5000000000 : ℝ)|^137 ≤ (3012163448129/25000000000000 : ℝ)^105
        have hw : |(-987597139/5000000000 : ℝ)|=(987597139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408478551/10000000000 : ℝ)|^137 ≤ (22423147754993/50000000000000 : ℝ)^105
        have hw : |(5408478551/10000000000 : ℝ)|=(5408478551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311697993/2500000000 : ℝ)|^137 ≤ (172420202761/400000000000 : ℝ)^105
        have hw : |(1311697993/2500000000 : ℝ)|=(1311697993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s6_1 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1336858077/2500000000 : ℝ)*x 0 + (-2057514957/10000000000 : ℝ)*x 1 + (2623395971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336858077/2500000000 : ℝ)^137 ≤ (22093490905467/50000000000000 : ℝ)^105 := by
    have hnat : (1336858077 : ℕ)^137*50000000000000^105 ≤ 22093490905467^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336858077 2500000000 22093490905467 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2057514957/10000000000 : ℝ)^137 ≤ (3176991952303/25000000000000 : ℝ)^105 := by
    have hnat : (2057514957 : ℕ)^137*25000000000000^105 ≤ 3176991952303^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057514957 10000000000 3176991952303 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623395971/5000000000 : ℝ)^137 ≤ (43105050368671/100000000000000 : ℝ)^105 := by
    have hnat : (2623395971 : ℕ)^137*100000000000000^105 ≤ 43105050368671^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623395971 5000000000 43105050368671 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336858077/2500000000 : ℝ), (-2057514957/10000000000 : ℝ), (2623395971/5000000000 : ℝ)] ![(22093490905467/50000000000000 : ℝ), (3176991952303/25000000000000 : ℝ), (43105050368671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336858077/2500000000 : ℝ)|^137 ≤ (22093490905467/50000000000000 : ℝ)^105
        have hw : |(1336858077/2500000000 : ℝ)|=(1336858077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2057514957/10000000000 : ℝ)|^137 ≤ (3176991952303/25000000000000 : ℝ)^105
        have hw : |(-2057514957/10000000000 : ℝ)|=(2057514957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623395971/5000000000 : ℝ)|^137 ≤ (43105050368671/100000000000000 : ℝ)^105
        have hw : |(2623395971/5000000000 : ℝ)|=(2623395971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s6_2 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (267371617/500000000 : ℝ)*x 0 + (1311697983/2500000000 : ℝ)*x 1 + (-2057514927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267371617/500000000 : ℝ)^137 ≤ (44186982155943/100000000000000 : ℝ)^105 := by
    have hnat : (267371617 : ℕ)^137*100000000000000^105 ≤ 44186982155943^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267371617 500000000 44186982155943 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311697983/2500000000 : ℝ)^137 ≤ (43105050261479/100000000000000 : ℝ)^105 := by
    have hnat : (1311697983 : ℕ)^137*100000000000000^105 ≤ 43105050261479^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311697983 2500000000 43105050261479 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057514927/10000000000 : ℝ)^137 ≤ (3176991891863/25000000000000 : ℝ)^105 := by
    have hnat : (2057514927 : ℕ)^137*25000000000000^105 ≤ 3176991891863^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057514927 10000000000 3176991891863 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267371617/500000000 : ℝ), (1311697983/2500000000 : ℝ), (-2057514927/10000000000 : ℝ)] ![(44186982155943/100000000000000 : ℝ), (43105050261479/100000000000000 : ℝ), (3176991891863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267371617/500000000 : ℝ)|^137 ≤ (44186982155943/100000000000000 : ℝ)^105
        have hw : |(267371617/500000000 : ℝ)|=(267371617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311697983/2500000000 : ℝ)|^137 ≤ (43105050261479/100000000000000 : ℝ)^105
        have hw : |(1311697983/2500000000 : ℝ)|=(1311697983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2057514927/10000000000 : ℝ)|^137 ≤ (3176991891863/25000000000000 : ℝ)^105
        have hw : |(-2057514927/10000000000 : ℝ)|=(2057514927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s6_3 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4204712/9765625 : ℝ)*x 0 + (2067122187/5000000000 : ℝ)*x 1 + (4483385919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204712/9765625 : ℝ)^137 ≤ (8326153212413/25000000000000 : ℝ)^105 := by
    have hnat : (4204712 : ℕ)^137*25000000000000^105 ≤ 8326153212413^105*9765625^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204712 9765625 8326153212413 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067122187/5000000000 : ℝ)^137 ≤ (31585539715371/100000000000000 : ℝ)^105 := by
    have hnat : (2067122187 : ℕ)^137*100000000000000^105 ≤ 31585539715371^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067122187 5000000000 31585539715371 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483385919/10000000000 : ℝ)^137 ≤ (4388730927123/12500000000000 : ℝ)^105 := by
    have hnat : (4483385919 : ℕ)^137*12500000000000^105 ≤ 4388730927123^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483385919 10000000000 4388730927123 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204712/9765625 : ℝ), (2067122187/5000000000 : ℝ), (4483385919/10000000000 : ℝ)] ![(8326153212413/25000000000000 : ℝ), (31585539715371/100000000000000 : ℝ), (4388730927123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204712/9765625 : ℝ)|^137 ≤ (8326153212413/25000000000000 : ℝ)^105
        have hw : |(4204712/9765625 : ℝ)|=(4204712/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2067122187/5000000000 : ℝ)|^137 ≤ (31585539715371/100000000000000 : ℝ)^105
        have hw : |(2067122187/5000000000 : ℝ)|=(2067122187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483385919/10000000000 : ℝ)|^137 ≤ (4388730927123/12500000000000 : ℝ)^105
        have hw : |(4483385919/10000000000 : ℝ)|=(4483385919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s6_4 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1975205779/10000000000 : ℝ)*x 0 + (5247374901/10000000000 : ℝ)*x 1 + (1351973127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1975205779/10000000000 : ℝ)^137 ≤ (6024372664683/50000000000000 : ℝ)^105 := by
    have hnat : (1975205779 : ℕ)^137*50000000000000^105 ≤ 6024372664683^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975205779 10000000000 6024372664683 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247374901/10000000000 : ℝ)^137 ≤ (21555649687369/50000000000000 : ℝ)^105 := by
    have hnat : (5247374901 : ℕ)^137*50000000000000^105 ≤ 21555649687369^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247374901 10000000000 21555649687369 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351973127/2500000000 : ℝ)^137 ≤ (44839955279551/100000000000000 : ℝ)^105 := by
    have hnat : (1351973127 : ℕ)^137*100000000000000^105 ≤ 44839955279551^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351973127 2500000000 44839955279551 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1975205779/10000000000 : ℝ), (5247374901/10000000000 : ℝ), (1351973127/2500000000 : ℝ)] ![(6024372664683/50000000000000 : ℝ), (21555649687369/50000000000000 : ℝ), (44839955279551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1975205779/10000000000 : ℝ)|^137 ≤ (6024372664683/50000000000000 : ℝ)^105
        have hw : |(-1975205779/10000000000 : ℝ)|=(1975205779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247374901/10000000000 : ℝ)|^137 ≤ (21555649687369/50000000000000 : ℝ)^105
        have hw : |(5247374901/10000000000 : ℝ)|=(5247374901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351973127/2500000000 : ℝ)|^137 ≤ (44839955279551/100000000000000 : ℝ)^105
        have hw : |(1351973127/2500000000 : ℝ)|=(1351973127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s6_5 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2652709197/5000000000 : ℝ)*x 0 + (-948207327/5000000000 : ℝ)*x 1 + (1081578549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652709197/5000000000 : ℝ)^137 ≤ (43734550931697/100000000000000 : ℝ)^105 := by
    have hnat : (2652709197 : ℕ)^137*100000000000000^105 ≤ 43734550931697^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652709197 5000000000 43734550931697 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948207327/5000000000 : ℝ)^137 ≤ (11425491208217/100000000000000 : ℝ)^105 := by
    have hnat : (948207327 : ℕ)^137*100000000000000^105 ≤ 11425491208217^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948207327 5000000000 11425491208217 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081578549/2000000000 : ℝ)^137 ≤ (5604994730443/12500000000000 : ℝ)^105 := by
    have hnat : (1081578549 : ℕ)^137*12500000000000^105 ≤ 5604994730443^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081578549 2000000000 5604994730443 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652709197/5000000000 : ℝ), (-948207327/5000000000 : ℝ), (1081578549/2000000000 : ℝ)] ![(43734550931697/100000000000000 : ℝ), (11425491208217/100000000000000 : ℝ), (5604994730443/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652709197/5000000000 : ℝ)|^137 ≤ (43734550931697/100000000000000 : ℝ)^105
        have hw : |(2652709197/5000000000 : ℝ)|=(2652709197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-948207327/5000000000 : ℝ)|^137 ≤ (11425491208217/100000000000000 : ℝ)^105
        have hw : |(-948207327/5000000000 : ℝ)|=(948207327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081578549/2000000000 : ℝ)|^137 ≤ (5604994730443/12500000000000 : ℝ)^105
        have hw : |(1081578549/2000000000 : ℝ)|=(1081578549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s6_6 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2652709393/5000000000 : ℝ)*x 0 + (5407892751/10000000000 : ℝ)*x 1 + (-1896414109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652709393/5000000000 : ℝ)^137 ≤ (43734555147909/100000000000000 : ℝ)^105 := by
    have hnat : (2652709393 : ℕ)^137*100000000000000^105 ≤ 43734555147909^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652709393 5000000000 43734555147909 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407892751/10000000000 : ℝ)^137 ≤ (8967991581691/20000000000000 : ℝ)^105 := by
    have hnat : (5407892751 : ℕ)^137*20000000000000^105 ≤ 8967991581691^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407892751 10000000000 8967991581691 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896414109/10000000000 : ℝ)^137 ≤ (11425486924021/100000000000000 : ℝ)^105 := by
    have hnat : (1896414109 : ℕ)^137*100000000000000^105 ≤ 11425486924021^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896414109 10000000000 11425486924021 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652709393/5000000000 : ℝ), (5407892751/10000000000 : ℝ), (-1896414109/10000000000 : ℝ)] ![(43734555147909/100000000000000 : ℝ), (8967991581691/20000000000000 : ℝ), (11425486924021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652709393/5000000000 : ℝ)|^137 ≤ (43734555147909/100000000000000 : ℝ)^105
        have hw : |(2652709393/5000000000 : ℝ)|=(2652709393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407892751/10000000000 : ℝ)|^137 ≤ (8967991581691/20000000000000 : ℝ)^105
        have hw : |(5407892751/10000000000 : ℝ)|=(5407892751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1896414109/10000000000 : ℝ)|^137 ≤ (11425486924021/100000000000000 : ℝ)^105
        have hw : |(-1896414109/10000000000 : ℝ)|=(1896414109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s6_7 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1076412433/2500000000 : ℝ)*x 0 + (896425469/2000000000 : ℝ)*x 1 + (4135509367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076412433/2500000000 : ℝ)^137 ≤ (16652430784917/50000000000000 : ℝ)^105 := by
    have hnat : (1076412433 : ℕ)^137*50000000000000^105 ≤ 16652430784917^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076412433 2500000000 16652430784917 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896425469/2000000000 : ℝ)^137 ≤ (17548494103869/50000000000000 : ℝ)^105 := by
    have hnat : (896425469 : ℕ)^137*50000000000000^105 ≤ 17548494103869^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896425469 2000000000 17548494103869 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4135509367/10000000000 : ℝ)^137 ≤ (31598150200543/100000000000000 : ℝ)^105 := by
    have hnat : (4135509367 : ℕ)^137*100000000000000^105 ≤ 31598150200543^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135509367 10000000000 31598150200543 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076412433/2500000000 : ℝ), (896425469/2000000000 : ℝ), (4135509367/10000000000 : ℝ)] ![(16652430784917/50000000000000 : ℝ), (17548494103869/50000000000000 : ℝ), (31598150200543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076412433/2500000000 : ℝ)|^137 ≤ (16652430784917/50000000000000 : ℝ)^105
        have hw : |(1076412433/2500000000 : ℝ)|=(1076412433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896425469/2000000000 : ℝ)|^137 ≤ (17548494103869/50000000000000 : ℝ)^105
        have hw : |(896425469/2000000000 : ℝ)|=(896425469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4135509367/10000000000 : ℝ)|^137 ≤ (31598150200543/100000000000000 : ℝ)^105
        have hw : |(4135509367/10000000000 : ℝ)|=(4135509367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1424_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1133/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5663/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5663/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5663/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5663/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5663/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5663/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5663/50000 : ℝ) ^ (4383/1024 : ℝ) ≤ (2234235885081219/25000000000000000000 : ℝ) := by
    have hpowers : (5663/50000 : ℝ)^4383 ≤ (2234235885081219/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5663 : ℕ)^4383*25000000000000000000^1024 ≤ 2234235885081219^1024*50000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5663 50000 2234235885081219 25000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5663/50000 : ℝ)) (X := (2234235885081219/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (4383/1024 : ℝ) ≤ (13873323425963641/50000000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^4383 ≤ (13873323425963641/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7379 : ℕ)^4383*50000000000000000000^1024 ≤ 13873323425963641^1024*50000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 13873323425963641 50000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (13873323425963641/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502234235885081219/12500000000000000000 : ℝ) ≤ (500020877945401/500000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (12502234235885081219/12500000000000000000 : ℝ)^1024 ≤ (500020877945401/500000000000000 : ℝ)^4383 := by
      have hnat : (12502234235885081219 : ℕ)^1024*500000000000000^4383 ≤ 500020877945401^4383*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502234235885081219 12500000000000000000 500020877945401 500000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500020877945401/500000000000000 : ℝ)) (X := (12502234235885081219/12500000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018341795196126079/50000000000000000000 : ℝ) ≤ (5000428459017569/5000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50018341795196126079/50000000000000000000 : ℝ)^1024 ≤ (5000428459017569/5000000000000000 : ℝ)^4383 := by
      have hnat : (50018341795196126079 : ℕ)^1024*5000000000000000^4383 ≤ 5000428459017569^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018341795196126079 50000000000000000000 5000428459017569 5000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000428459017569/5000000000000000 : ℝ)) (X := (50018341795196126079/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013873323425963641/25000000000000000000 : ℝ) ≤ (625081017322641/625000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (25013873323425963641/25000000000000000000 : ℝ)^1024 ≤ (625081017322641/625000000000000 : ℝ)^4383 := by
      have hnat : (25013873323425963641 : ℕ)^1024*625000000000000^4383 ≤ 625081017322641^4383*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013873323425963641 25000000000000000000 625081017322641 625000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625081017322641/625000000000000 : ℝ)) (X := (25013873323425963641/25000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2234235885081219/25000000000000000000 : ℝ) ≤ ((4288935087403105963/4290000000000000000 : ℝ)+2*(219679563559/171600000000000 : ℝ)*(5663/50000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (4288935087403105963/4290000000000000000 : ℝ)+2*(219679563559/171600000000000 : ℝ)*(5663/50000 : ℝ)=(500020877945401/500000000000000 : ℝ) by norm_num, show 1+2*(2234235885081219/25000000000000000000 : ℝ)=(12502234235885081219/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13873323425963641/50000000000000000000 : ℝ)+(2234235885081219/25000000000000000000 : ℝ) ≤ ((4288935087403105963/4290000000000000000 : ℝ)+(219679563559/171600000000000 : ℝ)*((7379/50000 : ℝ)+(5663/50000 : ℝ)))^(4383/1024 : ℝ) := by
    rw [show (4288935087403105963/4290000000000000000 : ℝ)+(219679563559/171600000000000 : ℝ)*((7379/50000 : ℝ)+(5663/50000 : ℝ))=(5000428459017569/5000000000000000 : ℝ) by norm_num, show 1+(13873323425963641/50000000000000000000 : ℝ)+(2234235885081219/25000000000000000000 : ℝ)=(50018341795196126079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13873323425963641/50000000000000000000 : ℝ) ≤ ((4288935087403105963/4290000000000000000 : ℝ)+2*(219679563559/171600000000000 : ℝ)*(7379/50000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (4288935087403105963/4290000000000000000 : ℝ)+2*(219679563559/171600000000000 : ℝ)*(7379/50000 : ℝ)=(625081017322641/625000000000000 : ℝ) by norm_num, show 1+2*(13873323425963641/50000000000000000000 : ℝ)=(25013873323425963641/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4288935087403105963/4290000000000000000 : ℝ)*(X 1 0+X 2 0)+(219679563559/171600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (4288935087403105963/4290000000000000000 : ℝ)) (alpha := (219679563559/171600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4288935087403105963/4290000000000000000 : ℝ)*(X 0 1+X 2 1)+(219679563559/171600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (4288935087403105963/4290000000000000000 : ℝ)) (alpha := (219679563559/171600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4288935087403105963/4290000000000000000 : ℝ)*(X 0 2+X 1 2)+(219679563559/171600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5663/50000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (4288935087403105963/4290000000000000000 : ℝ)) (alpha := (219679563559/171600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-987597139/5000000000 : ℝ)*X 0 0+(5408478551/10000000000 : ℝ)*X 0 1+(1311697993/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336858077/2500000000 : ℝ)*X 1 0+(-2057514957/10000000000 : ℝ)*X 1 1+(2623395971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267371617/500000000 : ℝ)*X 2 0+(1311697983/2500000000 : ℝ)*X 2 1+(-2057514927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4204712/9765625 : ℝ)*X 0 0+(2067122187/5000000000 : ℝ)*X 0 1+(4483385919/10000000000 : ℝ)*X 0 2+(4204712/9765625 : ℝ)*X 1 0+(2067122187/5000000000 : ℝ)*X 1 1+(4483385919/10000000000 : ℝ)*X 1 2+(4204712/9765625 : ℝ)*X 2 0+(2067122187/5000000000 : ℝ)*X 2 1+(4483385919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1975205779/10000000000 : ℝ)*X 0 0+(5247374901/10000000000 : ℝ)*X 0 1+(1351973127/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652709197/5000000000 : ℝ)*X 1 0+(-948207327/5000000000 : ℝ)*X 1 1+(1081578549/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652709393/5000000000 : ℝ)*X 2 0+(5407892751/10000000000 : ℝ)*X 2 1+(-1896414109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076412433/2500000000 : ℝ)*X 0 0+(896425469/2000000000 : ℝ)*X 0 1+(4135509367/10000000000 : ℝ)*X 0 2+(1076412433/2500000000 : ℝ)*X 1 0+(896425469/2000000000 : ℝ)*X 1 1+(4135509367/10000000000 : ℝ)*X 1 2+(1076412433/2500000000 : ℝ)*X 2 0+(896425469/2000000000 : ℝ)*X 2 1+(4135509367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3757616654738257959868687/1117187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (88465363/12500000000000 : ℝ)*(base19) + (672833779/100000000000000 : ℝ)*(base23) + (19224093/50000000000000 : ℝ)*(lower2) + (21885387/25000000000000 : ℝ)*(upper3) + (19821349/25000000000000 : ℝ)*(upper5) + (282781694515929/6250000000000 : ℝ)*(major0) + (282781694515929/6250000000000 : ℝ)*(major1) + (904901422450973/20000000000000 : ℝ)*(major2) + (1546204632016017/25000000000000 : ℝ)*(sp0) + (193276003616359/3125000000000 : ℝ)*(sp1) + (6184832150612613/100000000000000 : ℝ)*(sp2) + (286417427976619/10000000000000 : ℝ)*(sp3) + (3573845581/25000000000000 : ℝ)*(sp4) + (7009181773/100000000000000 : ℝ)*(sp7) + (2864181288947963/100000000000000 : ℝ)*(f.failure) + (773104102930799/12500000000000 : ℝ)*(f.sum) + (21650768012551/17160000000000000000000000000 : ℝ)*base65 + (239117372486816129/53625000000000000000000000000000 : ℝ)*base67 + (222110698859868001/85800000000000000000000000000000 : ℝ)*base70 + (125158524465941129/53625000000000000000000000000000 : ℝ)*base71 + (13741183935871/17160000000000000000000000000 : ℝ)*base73 + (575894251053731999/85800000000000000000000000000000 : ℝ)*base75 + (6446596023446791/8937500000000000000000000000000 : ℝ)*base78 + (162563119091865709/8937500000000000000000000000000 : ℝ)*base79 + (1226195637001/357500000000000000000000000 : ℝ)*base82 + (76909763/10000000000000000000000 : ℝ)*base89 + (76909763/10000000000000000000000 : ℝ)*base91 + (23090237/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43603895138423840862829849/17875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103413761/25000000000000 : ℝ)*(base23) + (2242563/5000000000000 : ℝ)*(lower2) + (147647487/100000000000000 : ℝ)*(upper3) + (33730719/50000000000000 : ℝ)*(upper4) + (11882769/12500000000000 : ℝ)*(upper5) + (4557440631311691/100000000000000 : ℝ)*(major0) + (4557440631311691/100000000000000 : ℝ)*(major1) + (1139360157827923/25000000000000 : ℝ)*(major2) + (4168361159/20000000000000 : ℝ)*(sp2) + (2472191013/100000000000000 : ℝ)*(sp3) + (6229851749853233/100000000000000 : ℝ)*(sp4) + (6229851749853233/100000000000000 : ℝ)*(sp5) + (1245966098878479/20000000000000 : ℝ)*(sp6) + (2885026959266503/100000000000000 : ℝ)*(sp7) + (721257357864379/25000000000000 : ℝ)*(f.failure) + (6229851749853233/100000000000000 : ℝ)*(f.sum) + (43238968498909/1320000000000000000000000000 : ℝ)*base65 + (2689362911620586567/429000000000000000000000000000000 : ℝ)*base68 + (59905101272373991/9750000000000000000000000000000 : ℝ)*base70 + (2290774188031413433/429000000000000000000000000000000 : ℝ)*base71 + (2355060661331/1320000000000000000000000000 : ℝ)*base74 + (8378459427123991/9750000000000000000000000000000 : ℝ)*base76 + (316691112556812811/143000000000000000000000000000000 : ℝ)*base77 + (1943467627139187189/143000000000000000000000000000000 : ℝ)*base80 + (2057895219343/2860000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (23363779/2500000000000000000000 : ℝ)*base89 + (23363779/2500000000000000000000 : ℝ)*base91 + (1636221/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1424_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1424_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1424_box_0 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1814171727/10000000000 : ℝ)*x 0 + (538647087/1000000000 : ℝ)*x 1 + (538647159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1814171727/10000000000 : ℝ)^137 ≤ (2695825757451/25000000000000 : ℝ)^105 := by
    have hnat : (1814171727 : ℕ)^137*25000000000000^105 ≤ 2695825757451^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814171727 10000000000 2695825757451 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538647087/1000000000 : ℝ)^137 ≤ (8921668917943/20000000000000 : ℝ)^105 := by
    have hnat : (538647087 : ℕ)^137*20000000000000^105 ≤ 8921668917943^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538647087 1000000000 8921668917943 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538647159/1000000000 : ℝ)^137 ≤ (22304176184821/50000000000000 : ℝ)^105 := by
    have hnat : (538647159 : ℕ)^137*50000000000000^105 ≤ 22304176184821^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538647159 1000000000 22304176184821 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1814171727/10000000000 : ℝ), (538647087/1000000000 : ℝ), (538647159/1000000000 : ℝ)] ![(2695825757451/25000000000000 : ℝ), (8921668917943/20000000000000 : ℝ), (22304176184821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1814171727/10000000000 : ℝ)|^137 ≤ (2695825757451/25000000000000 : ℝ)^105
        have hw : |(-1814171727/10000000000 : ℝ)|=(1814171727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538647087/1000000000 : ℝ)|^137 ≤ (8921668917943/20000000000000 : ℝ)^105
        have hw : |(538647087/1000000000 : ℝ)|=(538647087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538647159/1000000000 : ℝ)|^137 ≤ (22304176184821/50000000000000 : ℝ)^105
        have hw : |(538647159/1000000000 : ℝ)|=(538647159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_1 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1321506789/2500000000 : ℝ)*x 0 + (-1952147231/10000000000 : ℝ)*x 1 + (53864713/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321506789/2500000000 : ℝ)^137 ≤ (10881525498719/25000000000000 : ℝ)^105 := by
    have hnat : (1321506789 : ℕ)^137*25000000000000^105 ≤ 10881525498719^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321506789 2500000000 10881525498719 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952147231/10000000000 : ℝ)^137 ≤ (5932774378181/50000000000000 : ℝ)^105 := by
    have hnat : (1952147231 : ℕ)^137*50000000000000^105 ≤ 5932774378181^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952147231 10000000000 5932774378181 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53864713/100000000 : ℝ)^137 ≤ (2230417461803/5000000000000 : ℝ)^105 := by
    have hnat : (53864713 : ℕ)^137*5000000000000^105 ≤ 2230417461803^105*100000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53864713 100000000 2230417461803 5000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321506789/2500000000 : ℝ), (-1952147231/10000000000 : ℝ), (53864713/100000000 : ℝ)] ![(10881525498719/25000000000000 : ℝ), (5932774378181/50000000000000 : ℝ), (2230417461803/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321506789/2500000000 : ℝ)|^137 ≤ (10881525498719/25000000000000 : ℝ)^105
        have hw : |(1321506789/2500000000 : ℝ)|=(1321506789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952147231/10000000000 : ℝ)|^137 ≤ (5932774378181/50000000000000 : ℝ)^105
        have hw : |(-1952147231/10000000000 : ℝ)|=(1952147231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53864713/100000000 : ℝ)|^137 ≤ (2230417461803/5000000000000 : ℝ)^105
        have hw : |(53864713/100000000 : ℝ)|=(53864713/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_2 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5286027581/10000000000 : ℝ)*x 0 + (2693235561/5000000000 : ℝ)*x 1 + (-976073449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286027581/10000000000 : ℝ)^137 ≤ (1741044262437/4000000000000 : ℝ)^105 := by
    have hnat : (5286027581 : ℕ)^137*4000000000000^105 ≤ 1741044262437^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286027581 10000000000 1741044262437 4000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693235561/5000000000 : ℝ)^137 ≤ (44608347312689/100000000000000 : ℝ)^105 := by
    have hnat : (2693235561 : ℕ)^137*100000000000000^105 ≤ 44608347312689^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693235561 5000000000 44608347312689 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976073449/5000000000 : ℝ)^137 ≤ (11865546115469/100000000000000 : ℝ)^105 := by
    have hnat : (976073449 : ℕ)^137*100000000000000^105 ≤ 11865546115469^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976073449 5000000000 11865546115469 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286027581/10000000000 : ℝ), (2693235561/5000000000 : ℝ), (-976073449/5000000000 : ℝ)] ![(1741044262437/4000000000000 : ℝ), (44608347312689/100000000000000 : ℝ), (11865546115469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286027581/10000000000 : ℝ)|^137 ≤ (1741044262437/4000000000000 : ℝ)^105
        have hw : |(5286027581/10000000000 : ℝ)|=(5286027581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693235561/5000000000 : ℝ)|^137 ≤ (44608347312689/100000000000000 : ℝ)^105
        have hw : |(2693235561/5000000000 : ℝ)|=(2693235561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-976073449/5000000000 : ℝ)|^137 ≤ (11865546115469/100000000000000 : ℝ)^105
        have hw : |(-976073449/5000000000 : ℝ)|=(976073449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_3 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4452026553/10000000000 : ℝ)*x 0 + (1059036301/2500000000 : ℝ)*x 1 + (33094883/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4452026553/10000000000 : ℝ)^137 ≤ (8697442050713/25000000000000 : ℝ)^105 := by
    have hnat : (4452026553 : ℕ)^137*25000000000000^105 ≤ 8697442050713^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452026553 10000000000 8697442050713 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059036301/2500000000 : ℝ)^137 ≤ (652102335969/2000000000000 : ℝ)^105 := by
    have hnat : (1059036301 : ℕ)^137*2000000000000^105 ≤ 652102335969^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059036301 2500000000 652102335969 2000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33094883/78125000 : ℝ)^137 ≤ (16302557495391/50000000000000 : ℝ)^105 := by
    have hnat : (33094883 : ℕ)^137*50000000000000^105 ≤ 16302557495391^105*78125000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33094883 78125000 16302557495391 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4452026553/10000000000 : ℝ), (1059036301/2500000000 : ℝ), (33094883/78125000 : ℝ)] ![(8697442050713/25000000000000 : ℝ), (652102335969/2000000000000 : ℝ), (16302557495391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4452026553/10000000000 : ℝ)|^137 ≤ (8697442050713/25000000000000 : ℝ)^105
        have hw : |(4452026553/10000000000 : ℝ)|=(4452026553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059036301/2500000000 : ℝ)|^137 ≤ (652102335969/2000000000000 : ℝ)^105
        have hw : |(1059036301/2500000000 : ℝ)|=(1059036301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33094883/78125000 : ℝ)|^137 ≤ (16302557495391/50000000000000 : ℝ)^105
        have hw : |(33094883/78125000 : ℝ)|=(33094883/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_4 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138957423/10000000000 : ℝ)*x 0 + (5266450309/10000000000 : ℝ)*x 1 + (105329009/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138957423/10000000000 : ℝ)^137 ≤ (13368210274089/100000000000000 : ℝ)^105 := by
    have hnat : (2138957423 : ℕ)^137*100000000000000^105 ≤ 13368210274089^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138957423 10000000000 13368210274089 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266450309/10000000000 : ℝ)^137 ≤ (43315894097237/100000000000000 : ℝ)^105 := by
    have hnat : (5266450309 : ℕ)^137*100000000000000^105 ≤ 43315894097237^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266450309 10000000000 43315894097237 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105329009/200000000 : ℝ)^137 ≤ (43315895610379/100000000000000 : ℝ)^105 := by
    have hnat : (105329009 : ℕ)^137*100000000000000^105 ≤ 43315895610379^105*200000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105329009 200000000 43315895610379 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138957423/10000000000 : ℝ), (5266450309/10000000000 : ℝ), (105329009/200000000 : ℝ)] ![(13368210274089/100000000000000 : ℝ), (43315894097237/100000000000000 : ℝ), (43315895610379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138957423/10000000000 : ℝ)|^137 ≤ (13368210274089/100000000000000 : ℝ)^105
        have hw : |(-2138957423/10000000000 : ℝ)|=(2138957423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266450309/10000000000 : ℝ)|^137 ≤ (43315894097237/100000000000000 : ℝ)^105
        have hw : |(5266450309/10000000000 : ℝ)|=(5266450309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105329009/200000000 : ℝ)|^137 ≤ (43315895610379/100000000000000 : ℝ)^105
        have hw : |(105329009/200000000 : ℝ)|=(105329009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_5 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2685020713/5000000000 : ℝ)*x 0 + (-20008449/100000000 : ℝ)*x 1 + (1053289983/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685020713/5000000000 : ℝ)^137 ≤ (44430899541741/100000000000000 : ℝ)^105 := by
    have hnat : (2685020713 : ℕ)^137*100000000000000^105 ≤ 44430899541741^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685020713 5000000000 44430899541741 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20008449/100000000 : ℝ)^137 ≤ (490128422819/4000000000000 : ℝ)^105 := by
    have hnat : (20008449 : ℕ)^137*4000000000000^105 ≤ 490128422819^105*100000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20008449 100000000 490128422819 4000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053289983/2000000000 : ℝ)^137 ≤ (1353621558407/3125000000000 : ℝ)^105 := by
    have hnat : (1053289983 : ℕ)^137*3125000000000^105 ≤ 1353621558407^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053289983 2000000000 1353621558407 3125000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685020713/5000000000 : ℝ), (-20008449/100000000 : ℝ), (1053289983/2000000000 : ℝ)] ![(44430899541741/100000000000000 : ℝ), (490128422819/4000000000000 : ℝ), (1353621558407/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685020713/5000000000 : ℝ)|^137 ≤ (44430899541741/100000000000000 : ℝ)^105
        have hw : |(2685020713/5000000000 : ℝ)|=(2685020713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20008449/100000000 : ℝ)|^137 ≤ (490128422819/4000000000000 : ℝ)^105
        have hw : |(-20008449/100000000 : ℝ)|=(20008449/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053289983/2000000000 : ℝ)|^137 ≤ (1353621558407/3125000000000 : ℝ)^105
        have hw : |(1053289983/2000000000 : ℝ)|=(1053289983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_6 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5370040803/10000000000 : ℝ)*x 0 + (5266451071/10000000000 : ℝ)*x 1 + (-200084419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370040803/10000000000 : ℝ)^137 ≤ (44430892816207/100000000000000 : ℝ)^105 := by
    have hnat : (5370040803 : ℕ)^137*100000000000000^105 ≤ 44430892816207^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370040803 10000000000 44430892816207 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266451071/10000000000 : ℝ)^137 ≤ (21657951137321/50000000000000 : ℝ)^105 := by
    have hnat : (5266451071 : ℕ)^137*50000000000000^105 ≤ 21657951137321^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266451071 10000000000 21657951137321 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200084419/1000000000 : ℝ)^137 ≤ (12253204897301/100000000000000 : ℝ)^105 := by
    have hnat : (200084419 : ℕ)^137*100000000000000^105 ≤ 12253204897301^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200084419 1000000000 12253204897301 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370040803/10000000000 : ℝ), (5266451071/10000000000 : ℝ), (-200084419/1000000000 : ℝ)] ![(44430892816207/100000000000000 : ℝ), (21657951137321/50000000000000 : ℝ), (12253204897301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370040803/10000000000 : ℝ)|^137 ≤ (44430892816207/100000000000000 : ℝ)^105
        have hw : |(5370040803/10000000000 : ℝ)|=(5370040803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266451071/10000000000 : ℝ)|^137 ≤ (21657951137321/50000000000000 : ℝ)^105
        have hw : |(5266451071/10000000000 : ℝ)|=(5266451071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200084419/1000000000 : ℝ)|^137 ≤ (12253204897301/100000000000000 : ℝ)^105
        have hw : |(-200084419/1000000000 : ℝ)|=(200084419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_7 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (415818499/1000000000 : ℝ)*x 0 + (1095753637/2500000000 : ℝ)*x 1 + (1095753791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415818499/1000000000 : ℝ)^137 ≤ (3978049817491/12500000000000 : ℝ)^105 := by
    have hnat : (415818499 : ℕ)^137*12500000000000^105 ≤ 3978049817491^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415818499 1000000000 3978049817491 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095753637/2500000000 : ℝ)^137 ≤ (34087797599891/100000000000000 : ℝ)^105 := by
    have hnat : (1095753637 : ℕ)^137*100000000000000^105 ≤ 34087797599891^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095753637 2500000000 34087797599891 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095753791/2500000000 : ℝ)^137 ≤ (1363512154029/4000000000000 : ℝ)^105 := by
    have hnat : (1095753791 : ℕ)^137*4000000000000^105 ≤ 1363512154029^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095753791 2500000000 1363512154029 4000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415818499/1000000000 : ℝ), (1095753637/2500000000 : ℝ), (1095753791/2500000000 : ℝ)] ![(3978049817491/12500000000000 : ℝ), (34087797599891/100000000000000 : ℝ), (1363512154029/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415818499/1000000000 : ℝ)|^137 ≤ (3978049817491/12500000000000 : ℝ)^105
        have hw : |(415818499/1000000000 : ℝ)|=(415818499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095753637/2500000000 : ℝ)|^137 ≤ (34087797599891/100000000000000 : ℝ)^105
        have hw : |(1095753637/2500000000 : ℝ)|=(1095753637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095753791/2500000000 : ℝ)|^137 ≤ (1363512154029/4000000000000 : ℝ)^105
        have hw : |(1095753791/2500000000 : ℝ)|=(1095753791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_8 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2070558301/10000000000 : ℝ)*x 0 + (5183455361/10000000000 : ℝ)*x 1 + (2700224221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070558301/10000000000 : ℝ)^137 ≤ (512527257843/4000000000000 : ℝ)^105 := by
    have hnat : (2070558301 : ℕ)^137*4000000000000^105 ≤ 512527257843^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070558301 10000000000 512527257843 4000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183455361/10000000000 : ℝ)^137 ≤ (42427380240289/100000000000000 : ℝ)^105 := by
    have hnat : (5183455361 : ℕ)^137*100000000000000^105 ≤ 42427380240289^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183455361 10000000000 42427380240289 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700224221/5000000000 : ℝ)^137 ≤ (22379719150527/50000000000000 : ℝ)^105 := by
    have hnat : (2700224221 : ℕ)^137*50000000000000^105 ≤ 22379719150527^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700224221 5000000000 22379719150527 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2070558301/10000000000 : ℝ), (5183455361/10000000000 : ℝ), (2700224221/5000000000 : ℝ)] ![(512527257843/4000000000000 : ℝ), (42427380240289/100000000000000 : ℝ), (22379719150527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2070558301/10000000000 : ℝ)|^137 ≤ (512527257843/4000000000000 : ℝ)^105
        have hw : |(-2070558301/10000000000 : ℝ)|=(2070558301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183455361/10000000000 : ℝ)|^137 ≤ (42427380240289/100000000000000 : ℝ)^105
        have hw : |(5183455361/10000000000 : ℝ)|=(5183455361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700224221/5000000000 : ℝ)|^137 ≤ (22379719150527/50000000000000 : ℝ)^105
        have hw : |(2700224221/5000000000 : ℝ)|=(2700224221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_9 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5276238739/10000000000 : ℝ)*x 0 + (-1946349247/10000000000 : ℝ)*x 1 + (5400448927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276238739/10000000000 : ℝ)^137 ≤ (43420968403417/100000000000000 : ℝ)^105 := by
    have hnat : (5276238739 : ℕ)^137*100000000000000^105 ≤ 43420968403417^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276238739 10000000000 43420968403417 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946349247/10000000000 : ℝ)^137 ≤ (2954897009531/25000000000000 : ℝ)^105 := by
    have hnat : (1946349247 : ℕ)^137*25000000000000^105 ≤ 2954897009531^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946349247 10000000000 2954897009531 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400448927/10000000000 : ℝ)^137 ≤ (559493044323/1250000000000 : ℝ)^105 := by
    have hnat : (5400448927 : ℕ)^137*1250000000000^105 ≤ 559493044323^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400448927 10000000000 559493044323 1250000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276238739/10000000000 : ℝ), (-1946349247/10000000000 : ℝ), (5400448927/10000000000 : ℝ)] ![(43420968403417/100000000000000 : ℝ), (2954897009531/25000000000000 : ℝ), (559493044323/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276238739/10000000000 : ℝ)|^137 ≤ (43420968403417/100000000000000 : ℝ)^105
        have hw : |(5276238739/10000000000 : ℝ)|=(5276238739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1946349247/10000000000 : ℝ)|^137 ≤ (2954897009531/25000000000000 : ℝ)^105
        have hw : |(-1946349247/10000000000 : ℝ)|=(1946349247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400448927/10000000000 : ℝ)|^137 ≤ (559493044323/1250000000000 : ℝ)^105
        have hw : |(5400448927/10000000000 : ℝ)|=(5400448927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_10 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5276238717/10000000000 : ℝ)*x 0 + (270022451/500000000 : ℝ)*x 1 + (-38926983/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276238717/10000000000 : ℝ)^137 ≤ (4342096816719/10000000000000 : ℝ)^105 := by
    have hnat : (5276238717 : ℕ)^137*10000000000000^105 ≤ 4342096816719^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276238717 10000000000 4342096816719 10000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270022451/500000000 : ℝ)^137 ≤ (22379722275771/50000000000000 : ℝ)^105 := by
    have hnat : (270022451 : ℕ)^137*50000000000000^105 ≤ 22379722275771^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270022451 500000000 22379722275771 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38926983/200000000 : ℝ)^137 ≤ (738724204347/6250000000000 : ℝ)^105 := by
    have hnat : (38926983 : ℕ)^137*6250000000000^105 ≤ 738724204347^105*200000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38926983 200000000 738724204347 6250000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276238717/10000000000 : ℝ), (270022451/500000000 : ℝ), (-38926983/200000000 : ℝ)] ![(4342096816719/10000000000000 : ℝ), (22379722275771/50000000000000 : ℝ), (738724204347/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276238717/10000000000 : ℝ)|^137 ≤ (4342096816719/10000000000000 : ℝ)^105
        have hw : |(5276238717/10000000000 : ℝ)|=(5276238717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270022451/500000000 : ℝ)|^137 ≤ (22379722275771/50000000000000 : ℝ)^105
        have hw : |(270022451/500000000 : ℝ)|=(270022451/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38926983/200000000 : ℝ)|^137 ≤ (738724204347/6250000000000 : ℝ)^105
        have hw : |(-38926983/200000000 : ℝ)|=(38926983/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_11 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1121422407/2500000000 : ℝ)*x 0 + (4219026573/10000000000 : ℝ)*x 1 + (4219026343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1121422407/2500000000 : ℝ)^137 ≤ (7026677583633/20000000000000 : ℝ)^105 := by
    have hnat : (1121422407 : ℕ)^137*20000000000000^105 ≤ 7026677583633^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121422407 2500000000 7026677583633 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4219026573/10000000000 : ℝ)^137 ≤ (16216653593531/50000000000000 : ℝ)^105 := by
    have hnat : (4219026573 : ℕ)^137*50000000000000^105 ≤ 16216653593531^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219026573 10000000000 16216653593531 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4219026343/10000000000 : ℝ)^137 ≤ (32433304880113/100000000000000 : ℝ)^105 := by
    have hnat : (4219026343 : ℕ)^137*100000000000000^105 ≤ 32433304880113^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219026343 10000000000 32433304880113 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1121422407/2500000000 : ℝ), (4219026573/10000000000 : ℝ), (4219026343/10000000000 : ℝ)] ![(7026677583633/20000000000000 : ℝ), (16216653593531/50000000000000 : ℝ), (32433304880113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1121422407/2500000000 : ℝ)|^137 ≤ (7026677583633/20000000000000 : ℝ)^105
        have hw : |(1121422407/2500000000 : ℝ)|=(1121422407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4219026573/10000000000 : ℝ)|^137 ≤ (16216653593531/50000000000000 : ℝ)^105
        have hw : |(4219026573/10000000000 : ℝ)|=(4219026573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4219026343/10000000000 : ℝ)|^137 ≤ (32433304880113/100000000000000 : ℝ)^105
        have hw : |(4219026343/10000000000 : ℝ)|=(4219026343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_12 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-941379573/5000000000 : ℝ)*x 0 + (341714591/625000000 : ℝ)*x 1 + (5255326427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (941379573/5000000000 : ℝ)^137 ≤ (11318264464453/100000000000000 : ℝ)^105 := by
    have hnat : (941379573 : ℕ)^137*100000000000000^105 ≤ 11318264464453^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941379573 5000000000 11318264464453 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341714591/625000000 : ℝ)^137 ≤ (45485178960083/100000000000000 : ℝ)^105 := by
    have hnat : (341714591 : ℕ)^137*100000000000000^105 ≤ 45485178960083^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341714591 625000000 45485178960083 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255326427/10000000000 : ℝ)^137 ≤ (43196556563009/100000000000000 : ℝ)^105 := by
    have hnat : (5255326427 : ℕ)^137*100000000000000^105 ≤ 43196556563009^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255326427 10000000000 43196556563009 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-941379573/5000000000 : ℝ), (341714591/625000000 : ℝ), (5255326427/10000000000 : ℝ)] ![(11318264464453/100000000000000 : ℝ), (45485178960083/100000000000000 : ℝ), (43196556563009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-941379573/5000000000 : ℝ)|^137 ≤ (11318264464453/100000000000000 : ℝ)^105
        have hw : |(-941379573/5000000000 : ℝ)|=(941379573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341714591/625000000 : ℝ)|^137 ≤ (45485178960083/100000000000000 : ℝ)^105
        have hw : |(341714591/625000000 : ℝ)|=(341714591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255326427/10000000000 : ℝ)|^137 ≤ (43196556563009/100000000000000 : ℝ)^105
        have hw : |(5255326427/10000000000 : ℝ)|=(5255326427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_13 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2688912711/5000000000 : ℝ)*x 0 + (-1002629207/5000000000 : ℝ)*x 1 + (210213079/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688912711/5000000000 : ℝ)^137 ≤ (8902989889321/20000000000000 : ℝ)^105 := by
    have hnat : (2688912711 : ℕ)^137*20000000000000^105 ≤ 8902989889321^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688912711 5000000000 8902989889321 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002629207/5000000000 : ℝ)^137 ≤ (491539523881/4000000000000 : ℝ)^105 := by
    have hnat : (1002629207 : ℕ)^137*4000000000000^105 ≤ 491539523881^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002629207 5000000000 491539523881 4000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210213079/400000000 : ℝ)^137 ≤ (8639312488017/20000000000000 : ℝ)^105 := by
    have hnat : (210213079 : ℕ)^137*20000000000000^105 ≤ 8639312488017^105*400000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210213079 400000000 8639312488017 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688912711/5000000000 : ℝ), (-1002629207/5000000000 : ℝ), (210213079/400000000 : ℝ)] ![(8902989889321/20000000000000 : ℝ), (491539523881/4000000000000 : ℝ), (8639312488017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688912711/5000000000 : ℝ)|^137 ≤ (8902989889321/20000000000000 : ℝ)^105
        have hw : |(2688912711/5000000000 : ℝ)|=(2688912711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002629207/5000000000 : ℝ)|^137 ≤ (491539523881/4000000000000 : ℝ)^105
        have hw : |(-1002629207/5000000000 : ℝ)|=(1002629207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210213079/400000000 : ℝ)|^137 ≤ (8639312488017/20000000000000 : ℝ)^105
        have hw : |(210213079/400000000 : ℝ)|=(210213079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_14 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (26889127/50000000 : ℝ)*x 0 + (1313831763/2500000000 : ℝ)*x 1 + (-2005258341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26889127/50000000 : ℝ)^137 ≤ (22257474604501/50000000000000 : ℝ)^105 := by
    have hnat : (26889127 : ℕ)^137*50000000000000^105 ≤ 22257474604501^105*50000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26889127 50000000 22257474604501 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313831763/2500000000 : ℝ)^137 ≤ (21598281632939/50000000000000 : ℝ)^105 := by
    have hnat : (1313831763 : ℕ)^137*50000000000000^105 ≤ 21598281632939^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313831763 2500000000 21598281632939 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005258341/10000000000 : ℝ)^137 ≤ (2457697502667/20000000000000 : ℝ)^105 := by
    have hnat : (2005258341 : ℕ)^137*20000000000000^105 ≤ 2457697502667^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005258341 10000000000 2457697502667 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26889127/50000000 : ℝ), (1313831763/2500000000 : ℝ), (-2005258341/10000000000 : ℝ)] ![(22257474604501/50000000000000 : ℝ), (21598281632939/50000000000000 : ℝ), (2457697502667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26889127/50000000 : ℝ)|^137 ≤ (22257474604501/50000000000000 : ℝ)^105
        have hw : |(26889127/50000000 : ℝ)|=(26889127/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313831763/2500000000 : ℝ)|^137 ≤ (21598281632939/50000000000000 : ℝ)^105
        have hw : |(1313831763/2500000000 : ℝ)|=(1313831763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2005258341/10000000000 : ℝ)|^137 ≤ (2457697502667/20000000000000 : ℝ)^105
        have hw : |(-2005258341/10000000000 : ℝ)|=(2005258341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_box_15 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (206525087/500000000 : ℝ)*x 0 + (4396615473/10000000000 : ℝ)*x 1 + (879323247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206525087/500000000 : ℝ)^137 ≤ (157741184823/500000000000 : ℝ)^105 := by
    have hnat : (206525087 : ℕ)^137*500000000000^105 ≤ 157741184823^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206525087 500000000 157741184823 500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4396615473/10000000000 : ℝ)^137 ≤ (17112938820197/50000000000000 : ℝ)^105 := by
    have hnat : (4396615473 : ℕ)^137*50000000000000^105 ≤ 17112938820197^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396615473 10000000000 17112938820197 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879323247/2000000000 : ℝ)^137 ≤ (34225885380063/100000000000000 : ℝ)^105 := by
    have hnat : (879323247 : ℕ)^137*100000000000000^105 ≤ 34225885380063^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879323247 2000000000 34225885380063 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206525087/500000000 : ℝ), (4396615473/10000000000 : ℝ), (879323247/2000000000 : ℝ)] ![(157741184823/500000000000 : ℝ), (17112938820197/50000000000000 : ℝ), (34225885380063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206525087/500000000 : ℝ)|^137 ≤ (157741184823/500000000000 : ℝ)^105
        have hw : |(206525087/500000000 : ℝ)|=(206525087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4396615473/10000000000 : ℝ)|^137 ≤ (17112938820197/50000000000000 : ℝ)^105
        have hw : |(4396615473/10000000000 : ℝ)|=(4396615473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879323247/2000000000 : ℝ)|^137 ≤ (34225885380063/100000000000000 : ℝ)^105
        have hw : |(879323247/2000000000 : ℝ)|=(879323247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1424_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3931/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59103/100000 : ℝ) ∧ (80421/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42333/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1133/10000 : ℝ) ^ (4383/1024 : ℝ) ≤ (1790092202725961/20000000000000000000 : ℝ) := by
    have hpowers : (1133/10000 : ℝ)^4383 ≤ (1790092202725961/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1133 : ℕ)^4383*20000000000000000000^1024 ≤ 1790092202725961^1024*10000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1133 10000 1790092202725961 20000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1133/10000 : ℝ)) (X := (1790092202725961/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (4383/1024 : ℝ) ≤ (27714471638168973/100000000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^4383 ≤ (27714471638168973/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7377 : ℕ)^4383*100000000000000000000^1024 ≤ 27714471638168973^1024*50000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 27714471638168973 100000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (27714471638168973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001790092202725961/10000000000000000000 : ℝ) ≤ (1250052273804841/1250000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (10001790092202725961/10000000000000000000 : ℝ)^1024 ≤ (1250052273804841/1250000000000000 : ℝ)^4383 := by
      have hnat : (10001790092202725961 : ℕ)^1024*1250000000000000^4383 ≤ 1250052273804841^4383*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001790092202725961 10000000000000000000 1250052273804841 1250000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250052273804841/1250000000000000 : ℝ)) (X := (10001790092202725961/10000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018332466325899389/50000000000000000000 : ℝ) ≤ (5000428241128473/5000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50018332466325899389/50000000000000000000 : ℝ)^1024 ≤ (5000428241128473/5000000000000000 : ℝ)^4383 := by
      have hnat : (50018332466325899389 : ℕ)^1024*5000000000000000^4383 ≤ 5000428241128473^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018332466325899389 50000000000000000000 5000428241128473 5000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000428241128473/5000000000000000 : ℝ)) (X := (50018332466325899389/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027714471638168973/50000000000000000000 : ℝ) ≤ (2500323693518791/2500000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50027714471638168973/50000000000000000000 : ℝ)^1024 ≤ (2500323693518791/2500000000000000 : ℝ)^4383 := by
      have hnat : (50027714471638168973 : ℕ)^1024*2500000000000000^4383 ≤ 2500323693518791^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027714471638168973 50000000000000000000 2500323693518791 2500000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500323693518791/2500000000000000 : ℝ)) (X := (50027714471638168973/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1790092202725961/20000000000000000000 : ℝ) ≤ ((4278937523932673099/4280000000000000000 : ℝ)+2*(219145909109/171200000000000 : ℝ)*(1133/10000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (4278937523932673099/4280000000000000000 : ℝ)+2*(219145909109/171200000000000 : ℝ)*(1133/10000 : ℝ)=(1250052273804841/1250000000000000 : ℝ) by norm_num, show 1+2*(1790092202725961/20000000000000000000 : ℝ)=(10001790092202725961/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27714471638168973/100000000000000000000 : ℝ)+(1790092202725961/20000000000000000000 : ℝ) ≤ ((4278937523932673099/4280000000000000000 : ℝ)+(219145909109/171200000000000 : ℝ)*((7377/50000 : ℝ)+(1133/10000 : ℝ)))^(4383/1024 : ℝ) := by
    rw [show (4278937523932673099/4280000000000000000 : ℝ)+(219145909109/171200000000000 : ℝ)*((7377/50000 : ℝ)+(1133/10000 : ℝ))=(5000428241128473/5000000000000000 : ℝ) by norm_num, show 1+(27714471638168973/100000000000000000000 : ℝ)+(1790092202725961/20000000000000000000 : ℝ)=(50018332466325899389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27714471638168973/100000000000000000000 : ℝ) ≤ ((4278937523932673099/4280000000000000000 : ℝ)+2*(219145909109/171200000000000 : ℝ)*(7377/50000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (4278937523932673099/4280000000000000000 : ℝ)+2*(219145909109/171200000000000 : ℝ)*(7377/50000 : ℝ)=(2500323693518791/2500000000000000 : ℝ) by norm_num, show 1+2*(27714471638168973/100000000000000000000 : ℝ)=(50027714471638168973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4278937523932673099/4280000000000000000 : ℝ)*(X 1 0+X 2 0)+(219145909109/171200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (4278937523932673099/4280000000000000000 : ℝ)) (alpha := (219145909109/171200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4278937523932673099/4280000000000000000 : ℝ)*(X 0 1+X 2 1)+(219145909109/171200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (4278937523932673099/4280000000000000000 : ℝ)) (alpha := (219145909109/171200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4278937523932673099/4280000000000000000 : ℝ)*(X 0 2+X 1 2)+(219145909109/171200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (4278937523932673099/4280000000000000000 : ℝ)) (alpha := (219145909109/171200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1814171727/10000000000 : ℝ)*X 0 0+(538647087/1000000000 : ℝ)*X 0 1+(538647159/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321506789/2500000000 : ℝ)*X 1 0+(-1952147231/10000000000 : ℝ)*X 1 1+(53864713/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286027581/10000000000 : ℝ)*X 2 0+(2693235561/5000000000 : ℝ)*X 2 1+(-976073449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4452026553/10000000000 : ℝ)*X 0 0+(1059036301/2500000000 : ℝ)*X 0 1+(33094883/78125000 : ℝ)*X 0 2+(4452026553/10000000000 : ℝ)*X 1 0+(1059036301/2500000000 : ℝ)*X 1 1+(33094883/78125000 : ℝ)*X 1 2+(4452026553/10000000000 : ℝ)*X 2 0+(1059036301/2500000000 : ℝ)*X 2 1+(33094883/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2138957423/10000000000 : ℝ)*X 0 0+(5266450309/10000000000 : ℝ)*X 0 1+(105329009/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685020713/5000000000 : ℝ)*X 1 0+(-20008449/100000000 : ℝ)*X 1 1+(1053289983/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370040803/10000000000 : ℝ)*X 2 0+(5266451071/10000000000 : ℝ)*X 2 1+(-200084419/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((415818499/1000000000 : ℝ)*X 0 0+(1095753637/2500000000 : ℝ)*X 0 1+(1095753791/2500000000 : ℝ)*X 0 2+(415818499/1000000000 : ℝ)*X 1 0+(1095753637/2500000000 : ℝ)*X 1 1+(1095753791/2500000000 : ℝ)*X 1 2+(415818499/1000000000 : ℝ)*X 2 0+(1095753637/2500000000 : ℝ)*X 2 1+(1095753791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2070558301/10000000000 : ℝ)*X 0 0+(5183455361/10000000000 : ℝ)*X 0 1+(2700224221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276238739/10000000000 : ℝ)*X 1 0+(-1946349247/10000000000 : ℝ)*X 1 1+(5400448927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276238717/10000000000 : ℝ)*X 2 0+(270022451/500000000 : ℝ)*X 2 1+(-38926983/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1121422407/2500000000 : ℝ)*X 0 0+(4219026573/10000000000 : ℝ)*X 0 1+(4219026343/10000000000 : ℝ)*X 0 2+(1121422407/2500000000 : ℝ)*X 1 0+(4219026573/10000000000 : ℝ)*X 1 1+(4219026343/10000000000 : ℝ)*X 1 2+(1121422407/2500000000 : ℝ)*X 2 0+(4219026573/10000000000 : ℝ)*X 2 1+(4219026343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-941379573/5000000000 : ℝ)*X 0 0+(341714591/625000000 : ℝ)*X 0 1+(5255326427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688912711/5000000000 : ℝ)*X 1 0+(-1002629207/5000000000 : ℝ)*X 1 1+(210213079/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((26889127/50000000 : ℝ)*X 2 0+(1313831763/2500000000 : ℝ)*X 2 1+(-2005258341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((206525087/500000000 : ℝ)*X 0 0+(4396615473/10000000000 : ℝ)*X 0 1+(879323247/2000000000 : ℝ)*X 0 2+(206525087/500000000 : ℝ)*X 1 0+(4396615473/10000000000 : ℝ)*X 1 1+(879323247/2000000000 : ℝ)*X 1 2+(206525087/500000000 : ℝ)*X 2 0+(4396615473/10000000000 : ℝ)*X 2 1+(879323247/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3931/6250 : ℝ) ≤ (-8412060753490596702610561719303/13375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37834497/50000000000000 : ℝ)*(lower1) + (83745799/100000000000000 : ℝ)*(lower2) + (75635783/50000000000000 : ℝ)*(lower3) + (3771933/20000000000000 : ℝ)*(lower4) + (188206130177933/6250000000000 : ℝ)*(major0) + (188206130177933/6250000000000 : ℝ)*(major1) + (188206130177933/6250000000000 : ℝ)*(major2) + (3035767821/25000000000000 : ℝ)*(sp1) + (517162139105413/12500000000000 : ℝ)*(sp4) + (206864248488601/5000000000000 : ℝ)*(sp5) + (1034253426560863/25000000000000 : ℝ)*(sp6) + (953114683072679/50000000000000 : ℝ)*(sp7) + (70851649963/25000000000000 : ℝ)*(sp14) + (4290512133/12500000000000 : ℝ)*(sp15) + (953131845121211/50000000000000 : ℝ)*(f.failure) + (517162139105413/12500000000000 : ℝ)*(f.sum) + (4316476378883/535000000000000000000000000 : ℝ)*base66 + (199890875998949367/26750000000000000000000000000000 : ℝ)*base67 + (111123430968949367/26750000000000000000000000000000 : ℝ)*base69 + (25405007327949367/26750000000000000000000000000000 : ℝ)*base71 + (576293874123/535000000000000000000000000 : ℝ)*base74 + (156912992243949367/26750000000000000000000000000000 : ℝ)*base75 + (154609542146949367/26750000000000000000000000000000 : ℝ)*base77 + (239813847693949367/26750000000000000000000000000000 : ℝ)*base79 + (1887742845203/535000000000000000000000000 : ℝ)*base82 + (22904189/5000000000000000000000 : ℝ)*base90 + (22904189/5000000000000000000000 : ℝ)*base92 + (22904189/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59103/100000 : ℝ) ≤ (126485977673523527077300204880703/214000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97874439/100000000000000 : ℝ)*(lower3) + (177409517/100000000000000 : ℝ)*(upper4) + (143207/2000000000000 : ℝ)*(upper5) + (770685656385473/25000000000000 : ℝ)*(major0) + (770685656385473/25000000000000 : ℝ)*(major1) + (3082742625541893/100000000000000 : ℝ)*(major2) + (838857363887999/20000000000000 : ℝ)*(sp0) + (1048572064855029/25000000000000 : ℝ)*(sp1) + (10485720900731/250000000000 : ℝ)*(sp2) + (975743542715643/50000000000000 : ℝ)*(sp3) + (4382868297/100000000000000 : ℝ)*(sp5) + (2140998007/50000000000000 : ℝ)*(sp6) + (3657682843/100000000000000 : ℝ)*(sp7) + (5822848419/100000000000000 : ℝ)*(sp12) + (121968171444633/6250000000000 : ℝ)*(f.failure) + (2097146321144207/50000000000000 : ℝ)*(f.sum) + (5902325644377/3424000000000000000000000000 : ℝ)*base65 + (1193032751841652923/107000000000000000000000000000000 : ℝ)*base68 + (305300592442336407/428000000000000000000000000000000 : ℝ)*base69 + (355406906490347077/107000000000000000000000000000000 : ℝ)*base71 + (52325731347/27392000000000000000000000 : ℝ)*base74 + (260187427066336407/428000000000000000000000000000000 : ℝ)*base75 + (663244072009584173/107000000000000000000000000000000 : ℝ)*base78 + (1192942086333584173/107000000000000000000000000000000 : ℝ)*base80 + (6485790905717/2140000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1031567/625000000000000000000 : ℝ)*base90 + (1031567/625000000000000000000 : ℝ)*base92 + (7281567/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80421/100000 : ℝ) ≤ (172106001106267746409687993524633/214000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21971163/20000000000000 : ℝ)*(upper0) + (70869201/50000000000000 : ℝ)*(upper1) + (17916409/50000000000000 : ℝ)*(upper4) + (339091521754231/10000000000000 : ℝ)*(major0) + (339091521754231/10000000000000 : ℝ)*(major1) + (3390915217542311/100000000000000 : ℝ)*(major2) + (144083493879/50000000000000 : ℝ)*(sp1) + (335116787473/100000000000000 : ℝ)*(sp2) + (44148078569/100000000000000 : ℝ)*(sp3) + (2801607371/100000000000000 : ℝ)*(sp4) + (1152111097239879/25000000000000 : ℝ)*(sp8) + (460815902357913/10000000000000 : ℝ)*(sp9) + (921622414755883/20000000000000 : ℝ)*(sp10) + (2146531308104847/100000000000000 : ℝ)*(sp11) + (268321932022927/12500000000000 : ℝ)*(f.failure) + (576055898820861/12500000000000 : ℝ)*(f.sum) + (40669445274191/17120000000000000000000000000 : ℝ)*base66 + (186439473288779369/42800000000000000000000000000000 : ℝ)*base67 + (8024353113736741789/428000000000000000000000000000000 : ℝ)*base69 + (188356598664420631/42800000000000000000000000000000 : ℝ)*base72 + (13555469025809/17120000000000000000000000000 : ℝ)*base73 + (5320720817672741789/428000000000000000000000000000000 : ℝ)*base75 + (47169269577193131/42800000000000000000000000000000 : ℝ)*base78 + (55908646621206869/42800000000000000000000000000000 : ℝ)*base79 + (685819378091/856000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3115127/1250000000000000000000 : ℝ)*base89 + (3115127/1250000000000000000000 : ℝ)*base91 + (9384873/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42333/50000 : ℝ) ≤ (-2830937194551404908019419625829/3343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11152893/12500000000000 : ℝ)*(lower1) + (163478987/100000000000000 : ℝ)*(upper3) + (14014881/50000000000000 : ℝ)*(lower4) + (142028669/50000000000000 : ℝ)*(upper5) + (428540032136597/12500000000000 : ℝ)*(major0) + (428540032136597/12500000000000 : ℝ)*(major1) + (3428320257092777/100000000000000 : ℝ)*(major2) + (5086611171/100000000000000 : ℝ)*(sp4) + (907310979/4000000000000 : ℝ)*(sp6) + (70688130271/100000000000000 : ℝ)*(sp7) + (942920474169701/20000000000000 : ℝ)*(sp12) + (188584298298387/4000000000000 : ℝ)*(sp13) + (11786461936713/250000000000 : ℝ)*(sp14) + (2170183549351251/100000000000000 : ℝ)*(sp15) + (2170254237481521/100000000000000 : ℝ)*(f.failure) + (188584298298387/4000000000000 : ℝ)*(f.sum) + (34769119732763/17120000000000000000000000000 : ℝ)*base66 + (87462481523988159/6687500000000000000000000000000 : ℝ)*base68 + (3199650349522294077/428000000000000000000000000000000 : ℝ)*base70 + (80100162818363159/6687500000000000000000000000000 : ℝ)*base72 + (105681423428443/17120000000000000000000000000 : ℝ)*base74 + (320943027357705923/428000000000000000000000000000000 : ℝ)*base75 + (524113851775370897/53500000000000000000000000000000 : ℝ)*base78 + (424263586478870897/53500000000000000000000000000000 : ℝ)*base80 + (755241435457/1070000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (35722121/10000000000000000000000 : ℝ)*base89 + (35722121/10000000000000000000000 : ℝ)*base91 + (64277879/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1424_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3931/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59103/100000 : ℝ) else (80421/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42333/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1424_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1424_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3931/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59103/100000 : ℝ) else (80421/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42333/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1424_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1424_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3931/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59103/100000 : ℝ) else (80421/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42333/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1424_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
