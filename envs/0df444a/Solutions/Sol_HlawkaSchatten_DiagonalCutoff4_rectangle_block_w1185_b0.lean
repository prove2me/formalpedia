-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1185_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:51:15.069268+00:00
-- url     : https://prove2.me/submissions/62afebfd-197d-496c-ac1c-728a5c4d2d48

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
theorem support_rectangle_w1185_s0_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878275639/10000000000 : ℝ)*x 0 + (1511111241/2500000000 : ℝ)*x 1 + (4785886483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878275639/10000000000 : ℝ)^4189 ≤ (10934334582583/100000000000000 : ℝ)^3165 := by
    have hnat : (1878275639 : ℕ)^4189*100000000000000^3165 ≤ 10934334582583^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878275639 10000000000 10934334582583 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1511111241/2500000000 : ℝ)^4189 ≤ (6419878108973/12500000000000 : ℝ)^3165 := by
    have hnat : (1511111241 : ℕ)^4189*12500000000000^3165 ≤ 6419878108973^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511111241 2500000000 6419878108973 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785886483/10000000000 : ℝ)^4189 ≤ (37706640524479/100000000000000 : ℝ)^3165 := by
    have hnat : (4785886483 : ℕ)^4189*100000000000000^3165 ≤ 37706640524479^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785886483 10000000000 37706640524479 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878275639/10000000000 : ℝ), (1511111241/2500000000 : ℝ), (4785886483/10000000000 : ℝ)] ![(10934334582583/100000000000000 : ℝ), (6419878108973/12500000000000 : ℝ), (37706640524479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878275639/10000000000 : ℝ)|^4189 ≤ (10934334582583/100000000000000 : ℝ)^3165
        have hw : |(-1878275639/10000000000 : ℝ)|=(1878275639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1511111241/2500000000 : ℝ)|^4189 ≤ (6419878108973/12500000000000 : ℝ)^3165
        have hw : |(1511111241/2500000000 : ℝ)|=(1511111241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785886483/10000000000 : ℝ)|^4189 ≤ (37706640524479/100000000000000 : ℝ)^3165
        have hw : |(4785886483/10000000000 : ℝ)|=(4785886483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s0_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5514370999/10000000000 : ℝ)*x 0 + (-649833937/2500000000 : ℝ)*x 1 + (4785886489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514370999/10000000000 : ℝ)^4189 ≤ (11371033391321/25000000000000 : ℝ)^3165 := by
    have hnat : (5514370999 : ℕ)^4189*25000000000000^3165 ≤ 11371033391321^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514370999 10000000000 11371033391321 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649833937/2500000000 : ℝ)^4189 ≤ (16809225827497/100000000000000 : ℝ)^3165 := by
    have hnat : (649833937 : ℕ)^4189*100000000000000^3165 ≤ 16809225827497^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649833937 2500000000 16809225827497 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785886489/10000000000 : ℝ)^4189 ≤ (18853320293523/50000000000000 : ℝ)^3165 := by
    have hnat : (4785886489 : ℕ)^4189*50000000000000^3165 ≤ 18853320293523^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785886489 10000000000 18853320293523 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514370999/10000000000 : ℝ), (-649833937/2500000000 : ℝ), (4785886489/10000000000 : ℝ)] ![(11371033391321/25000000000000 : ℝ), (16809225827497/100000000000000 : ℝ), (18853320293523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514370999/10000000000 : ℝ)|^4189 ≤ (11371033391321/25000000000000 : ℝ)^3165
        have hw : |(5514370999/10000000000 : ℝ)|=(5514370999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-649833937/2500000000 : ℝ)|^4189 ≤ (16809225827497/100000000000000 : ℝ)^3165
        have hw : |(-649833937/2500000000 : ℝ)|=(649833937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785886489/10000000000 : ℝ)|^4189 ≤ (18853320293523/50000000000000 : ℝ)^3165
        have hw : |(4785886489/10000000000 : ℝ)|=(4785886489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s0_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1378592743/2500000000 : ℝ)*x 0 + (598235811/1250000000 : ℝ)*x 1 + (-519867157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378592743/2500000000 : ℝ)^4189 ≤ (45484133270527/100000000000000 : ℝ)^3165 := by
    have hnat : (1378592743 : ℕ)^4189*100000000000000^3165 ≤ 45484133270527^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378592743 2500000000 45484133270527 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598235811/1250000000 : ℝ)^4189 ≤ (18853320288309/50000000000000 : ℝ)^3165 := by
    have hnat : (598235811 : ℕ)^4189*50000000000000^3165 ≤ 18853320288309^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598235811 1250000000 18853320288309 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519867157/2000000000 : ℝ)^4189 ≤ (840461307209/5000000000000 : ℝ)^3165 := by
    have hnat : (519867157 : ℕ)^4189*5000000000000^3165 ≤ 840461307209^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519867157 2000000000 840461307209 5000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378592743/2500000000 : ℝ), (598235811/1250000000 : ℝ), (-519867157/2000000000 : ℝ)] ![(45484133270527/100000000000000 : ℝ), (18853320288309/50000000000000 : ℝ), (840461307209/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378592743/2500000000 : ℝ)|^4189 ≤ (45484133270527/100000000000000 : ℝ)^3165
        have hw : |(1378592743/2500000000 : ℝ)|=(1378592743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598235811/1250000000 : ℝ)|^4189 ≤ (18853320288309/50000000000000 : ℝ)^3165
        have hw : |(598235811/1250000000 : ℝ)|=(598235811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519867157/2000000000 : ℝ)|^4189 ≤ (840461307209/5000000000000 : ℝ)^3165
        have hw : |(-519867157/2000000000 : ℝ)|=(519867157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s0_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4197535351/10000000000 : ℝ)*x 0 + (623833959/2000000000 : ℝ)*x 1 + (2822087467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197535351/10000000000 : ℝ)^4189 ≤ (31697020941263/100000000000000 : ℝ)^3165 := by
    have hnat : (4197535351 : ℕ)^4189*100000000000000^3165 ≤ 31697020941263^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197535351 10000000000 31697020941263 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623833959/2000000000 : ℝ)^4189 ≤ (10698208552587/50000000000000 : ℝ)^3165 := by
    have hnat : (623833959 : ℕ)^4189*50000000000000^3165 ≤ 10698208552587^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623833959 2000000000 10698208552587 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2822087467/5000000000 : ℝ)^4189 ≤ (46906561945381/100000000000000 : ℝ)^3165 := by
    have hnat : (2822087467 : ℕ)^4189*100000000000000^3165 ≤ 46906561945381^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822087467 5000000000 46906561945381 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197535351/10000000000 : ℝ), (623833959/2000000000 : ℝ), (2822087467/5000000000 : ℝ)] ![(31697020941263/100000000000000 : ℝ), (10698208552587/50000000000000 : ℝ), (46906561945381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197535351/10000000000 : ℝ)|^4189 ≤ (31697020941263/100000000000000 : ℝ)^3165
        have hw : |(4197535351/10000000000 : ℝ)|=(4197535351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623833959/2000000000 : ℝ)|^4189 ≤ (10698208552587/50000000000000 : ℝ)^3165
        have hw : |(623833959/2000000000 : ℝ)|=(623833959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2822087467/5000000000 : ℝ)|^4189 ≤ (46906561945381/100000000000000 : ℝ)^3165
        have hw : |(2822087467/5000000000 : ℝ)|=(2822087467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s0_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1883295911/10000000000 : ℝ)*x 0 + (2409165399/5000000000 : ℝ)*x 1 + (3005428449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1883295911/10000000000 : ℝ)^4189 ≤ (342907257159/3125000000000 : ℝ)^3165 := by
    have hnat : (1883295911 : ℕ)^4189*3125000000000^3165 ≤ 342907257159^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883295911 10000000000 342907257159 3125000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2409165399/5000000000 : ℝ)^4189 ≤ (594458333511/1562500000000 : ℝ)^3165 := by
    have hnat : (2409165399 : ℕ)^4189*1562500000000^3165 ≤ 594458333511^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409165399 5000000000 594458333511 1562500000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005428449/5000000000 : ℝ)^4189 ≤ (6372704301201/12500000000000 : ℝ)^3165 := by
    have hnat : (3005428449 : ℕ)^4189*12500000000000^3165 ≤ 6372704301201^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005428449 5000000000 6372704301201 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1883295911/10000000000 : ℝ), (2409165399/5000000000 : ℝ), (3005428449/5000000000 : ℝ)] ![(342907257159/3125000000000 : ℝ), (594458333511/1562500000000 : ℝ), (6372704301201/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1883295911/10000000000 : ℝ)|^4189 ≤ (342907257159/3125000000000 : ℝ)^3165
        have hw : |(-1883295911/10000000000 : ℝ)|=(1883295911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2409165399/5000000000 : ℝ)|^4189 ≤ (594458333511/1562500000000 : ℝ)^3165
        have hw : |(2409165399/5000000000 : ℝ)|=(2409165399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3005428449/5000000000 : ℝ)|^4189 ≤ (6372704301201/12500000000000 : ℝ)^3165
        have hw : |(3005428449/5000000000 : ℝ)|=(3005428449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s0_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20203863/39062500 : ℝ)*x 0 + (-54974623/400000000 : ℝ)*x 1 + (3005428289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20203863/39062500 : ℝ)^4189 ≤ (41786592716347/100000000000000 : ℝ)^3165 := by
    have hnat : (20203863 : ℕ)^4189*100000000000000^3165 ≤ 41786592716347^3165*39062500^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20203863 39062500 41786592716347 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54974623/400000000 : ℝ)^4189 ≤ (7062281693/97656250000 : ℝ)^3165 := by
    have hnat : (54974623 : ℕ)^4189*97656250000^3165 ≤ 7062281693^3165*400000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54974623 400000000 7062281693 97656250000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005428289/5000000000 : ℝ)^4189 ≤ (50981630817379/100000000000000 : ℝ)^3165 := by
    have hnat : (3005428289 : ℕ)^4189*100000000000000^3165 ≤ 50981630817379^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005428289 5000000000 50981630817379 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20203863/39062500 : ℝ), (-54974623/400000000 : ℝ), (3005428289/5000000000 : ℝ)] ![(41786592716347/100000000000000 : ℝ), (7062281693/97656250000 : ℝ), (50981630817379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20203863/39062500 : ℝ)|^4189 ≤ (41786592716347/100000000000000 : ℝ)^3165
        have hw : |(20203863/39062500 : ℝ)|=(20203863/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54974623/400000000 : ℝ)|^4189 ≤ (7062281693/97656250000 : ℝ)^3165
        have hw : |(-54974623/400000000 : ℝ)|=(54974623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3005428289/5000000000 : ℝ)|^4189 ≤ (50981630817379/100000000000000 : ℝ)^3165
        have hw : |(3005428289/5000000000 : ℝ)|=(3005428289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s0_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034437773/2000000000 : ℝ)*x 0 + (3005428377/5000000000 : ℝ)*x 1 + (-343591347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034437773/2000000000 : ℝ)^4189 ≤ (652915500667/1562500000000 : ℝ)^3165 := by
    have hnat : (1034437773 : ℕ)^4189*1562500000000^3165 ≤ 652915500667^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034437773 2000000000 652915500667 1562500000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3005428377/5000000000 : ℝ)^4189 ≤ (10196326558621/20000000000000 : ℝ)^3165 := by
    have hnat : (3005428377 : ℕ)^4189*20000000000000^3165 ≤ 10196326558621^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005428377 5000000000 10196326558621 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343591347/2500000000 : ℝ)^4189 ≤ (7231775151303/100000000000000 : ℝ)^3165 := by
    have hnat : (343591347 : ℕ)^4189*100000000000000^3165 ≤ 7231775151303^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343591347 2500000000 7231775151303 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034437773/2000000000 : ℝ), (3005428377/5000000000 : ℝ), (-343591347/2500000000 : ℝ)] ![(652915500667/1562500000000 : ℝ), (10196326558621/20000000000000 : ℝ), (7231775151303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034437773/2000000000 : ℝ)|^4189 ≤ (652915500667/1562500000000 : ℝ)^3165
        have hw : |(1034437773/2000000000 : ℝ)|=(1034437773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3005428377/5000000000 : ℝ)|^4189 ≤ (10196326558621/20000000000000 : ℝ)^3165
        have hw : |(3005428377/5000000000 : ℝ)|=(3005428377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343591347/2500000000 : ℝ)|^4189 ≤ (7231775151303/100000000000000 : ℝ)^3165
        have hw : |(-343591347/2500000000 : ℝ)|=(343591347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s0_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525950927/1250000000 : ℝ)*x 0 + (1115816501/2000000000 : ℝ)*x 1 + (637311361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525950927/1250000000 : ℝ)^4189 ≤ (31797725169589/100000000000000 : ℝ)^3165 := by
    have hnat : (525950927 : ℕ)^4189*100000000000000^3165 ≤ 31797725169589^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525950927 1250000000 31797725169589 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115816501/2000000000 : ℝ)^4189 ≤ (23095961114707/50000000000000 : ℝ)^3165 := by
    have hnat : (1115816501 : ℕ)^4189*50000000000000^3165 ≤ 23095961114707^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115816501 2000000000 23095961114707 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637311361/2000000000 : ℝ)^4189 ≤ (4402070517603/20000000000000 : ℝ)^3165 := by
    have hnat : (637311361 : ℕ)^4189*20000000000000^3165 ≤ 4402070517603^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637311361 2000000000 4402070517603 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525950927/1250000000 : ℝ), (1115816501/2000000000 : ℝ), (637311361/2000000000 : ℝ)] ![(31797725169589/100000000000000 : ℝ), (23095961114707/50000000000000 : ℝ), (4402070517603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525950927/1250000000 : ℝ)|^4189 ≤ (31797725169589/100000000000000 : ℝ)^3165
        have hw : |(525950927/1250000000 : ℝ)|=(525950927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115816501/2000000000 : ℝ)|^4189 ≤ (23095961114707/50000000000000 : ℝ)^3165
        have hw : |(1115816501/2000000000 : ℝ)|=(1115816501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637311361/2000000000 : ℝ)|^4189 ≤ (4402070517603/20000000000000 : ℝ)^3165
        have hw : |(637311361/2000000000 : ℝ)|=(637311361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (589/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27651/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8377/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8377 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8377*1^2048 ≤ 0^2048*1^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8377/2048 : ℝ) ≤ (2356639952175841711/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8377 ≤ (2356639952175841711/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8377*100000000000000000000^2048 ≤ 2356639952175841711^2048*5^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2356639952175841711 100000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2356639952175841711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8377 := by
      have hnat : (1 : ℕ)^2048*1^8377 ≤ 1^8377*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102356639952175841711/100000000000000000000 : ℝ) ≤ (10057108928027851/10000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (102356639952175841711/100000000000000000000 : ℝ)^2048 ≤ (10057108928027851/10000000000000000 : ℝ)^8377 := by
      have hnat : (102356639952175841711 : ℕ)^2048*10000000000000000^8377 ≤ 10057108928027851^8377*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102356639952175841711 100000000000000000000 10057108928027851 10000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057108928027851/10000000000000000 : ℝ)) (X := (102356639952175841711/100000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52356639952175841711/50000000000000000000 : ℝ) ≤ (5057108928027851/5000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (52356639952175841711/50000000000000000000 : ℝ)^2048 ≤ (5057108928027851/5000000000000000 : ℝ)^8377 := by
      have hnat : (52356639952175841711 : ℕ)^2048*5000000000000000^8377 ≤ 5057108928027851^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52356639952175841711 50000000000000000000 5057108928027851 5000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057108928027851/5000000000000000 : ℝ)) (X := (52356639952175841711/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57108928027851/4000000000000000 : ℝ)*(0 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(57108928027851/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2356639952175841711/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57108928027851/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (1 : ℝ)+(57108928027851/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057108928027851/10000000000000000 : ℝ) by norm_num, show 1+(2356639952175841711/100000000000000000000 : ℝ)+(0 : ℝ)=(102356639952175841711/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2356639952175841711/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57108928027851/4000000000000000 : ℝ)*(2/5 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(57108928027851/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057108928027851/5000000000000000 : ℝ) by norm_num, show 1+2*(2356639952175841711/100000000000000000000 : ℝ)=(52356639952175841711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57108928027851/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57108928027851/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57108928027851/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57108928027851/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57108928027851/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57108928027851/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1878275639/10000000000 : ℝ)*X 0 0+(1511111241/2500000000 : ℝ)*X 0 1+(4785886483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5514370999/10000000000 : ℝ)*X 1 0+(-649833937/2500000000 : ℝ)*X 1 1+(4785886489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378592743/2500000000 : ℝ)*X 2 0+(598235811/1250000000 : ℝ)*X 2 1+(-519867157/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197535351/10000000000 : ℝ)*X 0 0+(623833959/2000000000 : ℝ)*X 0 1+(2822087467/5000000000 : ℝ)*X 0 2+(4197535351/10000000000 : ℝ)*X 1 0+(623833959/2000000000 : ℝ)*X 1 1+(2822087467/5000000000 : ℝ)*X 1 2+(4197535351/10000000000 : ℝ)*X 2 0+(623833959/2000000000 : ℝ)*X 2 1+(2822087467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1883295911/10000000000 : ℝ)*X 0 0+(2409165399/5000000000 : ℝ)*X 0 1+(3005428449/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20203863/39062500 : ℝ)*X 1 0+(-54974623/400000000 : ℝ)*X 1 1+(3005428289/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034437773/2000000000 : ℝ)*X 2 0+(3005428377/5000000000 : ℝ)*X 2 1+(-343591347/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((525950927/1250000000 : ℝ)*X 0 0+(1115816501/2000000000 : ℝ)*X 0 1+(637311361/2000000000 : ℝ)*X 0 2+(525950927/1250000000 : ℝ)*X 1 0+(1115816501/2000000000 : ℝ)*X 1 1+(637311361/2000000000 : ℝ)*X 1 2+(525950927/1250000000 : ℝ)*X 2 0+(1115816501/2000000000 : ℝ)*X 2 1+(637311361/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145990013323573420809267/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61256541/100000000000000 : ℝ)*(base1) + (1429017643/100000000000000 : ℝ)*(base19) + (10634829/800000000000 : ℝ)*(base23) + (19154717/20000000000000 : ℝ)*(base24) + (16467191/5000000000000 : ℝ)*(upper3) + (297652699201939/50000000000000 : ℝ)*(major0) + (297652699201939/50000000000000 : ℝ)*(major1) + (297652699201939/50000000000000 : ℝ)*(major2) + (99320581488909/12500000000000 : ℝ)*(sp0) + (198641580065599/25000000000000 : ℝ)*(sp1) + (794566324152829/100000000000000 : ℝ)*(sp2) + (79208054807057/20000000000000 : ℝ)*(sp3) + (3158625309/100000000000000 : ℝ)*(sp4) + (1258791267/50000000000000 : ℝ)*(sp7) + (9901071321859/2500000000000 : ℝ)*(f.failure) + (794567749280039/100000000000000 : ℝ)*(f.sum) + (31995078003089/100000000000000000000000000000 : ℝ)*base65 + (1039140141796911/200000000000000000000000000000 : ℝ)*base68 + (2097974718396911/200000000000000000000000000000 : ℝ)*base70 + (729260291396911/200000000000000000000000000000 : ℝ)*base72 + (23488338496911/100000000000000000000000000000 : ℝ)*base74 + (972174675596911/200000000000000000000000000000 : ℝ)*base76 + (760585528196911/200000000000000000000000000000 : ℝ)*base78 + (168314894196911/200000000000000000000000000000 : ℝ)*base80 + (309533564296911/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (41329/12500000000000000000 : ℝ)*base90 + (41329/12500000000000000000 : ℝ)*base92 + (41329/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (975230326228781279730489/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26793941/50000000000000 : ℝ)*(base1) + (155427463/12500000000000 : ℝ)*(base19) + (1236718291/100000000000000 : ℝ)*(base23) + (128761873/100000000000000 : ℝ)*(upper3) + (151824139/100000000000000 : ℝ)*(upper5) + (628262329704371/100000000000000 : ℝ)*(major0) + (628262329704371/100000000000000 : ℝ)*(major1) + (628262329704371/100000000000000 : ℝ)*(major2) + (629018163/25000000000000 : ℝ)*(sp1) + (2569166897/100000000000000 : ℝ)*(sp2) + (13102440886949/1562500000000 : ℝ)*(sp4) + (838552403684497/100000000000000 : ℝ)*(sp5) + (167710471458333/20000000000000 : ℝ)*(sp6) + (417968280105613/100000000000000 : ℝ)*(sp7) + (83593666738699/20000000000000 : ℝ)*(f.failure) + (419278081588427/50000000000000 : ℝ)*(f.sum) + (193977417963279/200000000000000000000000000000 : ℝ)*base66 + (853027072763279/400000000000000000000000000000 : ℝ)*base68 + (2222169272763279/400000000000000000000000000000 : ℝ)*base70 + (1768271055636721/400000000000000000000000000000 : ℝ)*base71 + (1139900334363279/200000000000000000000000000000 : ℝ)*base74 + (118022260836721/400000000000000000000000000000 : ℝ)*base75 + (214111162363279/400000000000000000000000000000 : ℝ)*base78 + (2309691400036721/400000000000000000000000000000 : ℝ)*base79 + (1164620375563279/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (174631/100000000000000000000 : ℝ)*base89 + (174631/100000000000000000000 : ℝ)*base91 + (174631/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1185_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (589/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27651/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1185_s1_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079828557/10000000000 : ℝ)*x 0 + (569016833/1000000000 : ℝ)*x 1 + (15659817/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079828557/10000000000 : ℝ)^4189 ≤ (6256811254353/50000000000000 : ℝ)^3165 := by
    have hnat : (2079828557 : ℕ)^4189*50000000000000^3165 ≤ 6256811254353^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079828557 10000000000 6256811254353 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569016833/1000000000 : ℝ)^4189 ≤ (4741312829413/10000000000000 : ℝ)^3165 := by
    have hnat : (569016833 : ℕ)^4189*10000000000000^3165 ≤ 4741312829413^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569016833 1000000000 4741312829413 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15659817/31250000 : ℝ)^4189 ≤ (80146498361/200000000000 : ℝ)^3165 := by
    have hnat : (15659817 : ℕ)^4189*200000000000^3165 ≤ 80146498361^3165*31250000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15659817 31250000 80146498361 200000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079828557/10000000000 : ℝ), (569016833/1000000000 : ℝ), (15659817/31250000 : ℝ)] ![(6256811254353/50000000000000 : ℝ), (4741312829413/10000000000000 : ℝ), (80146498361/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079828557/10000000000 : ℝ)|^4189 ≤ (6256811254353/50000000000000 : ℝ)^3165
        have hw : |(-2079828557/10000000000 : ℝ)|=(2079828557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569016833/1000000000 : ℝ)|^4189 ≤ (4741312829413/10000000000000 : ℝ)^3165
        have hw : |(569016833/1000000000 : ℝ)|=(569016833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15659817/31250000 : ℝ)|^4189 ≤ (80146498361/200000000000 : ℝ)^3165
        have hw : |(15659817/31250000 : ℝ)|=(15659817/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s1_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5416765349/10000000000 : ℝ)*x 0 + (-2445473597/10000000000 : ℝ)*x 1 + (2505570839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416765349/10000000000 : ℝ)^4189 ≤ (22210821342757/50000000000000 : ℝ)^3165 := by
    have hnat : (5416765349 : ℕ)^4189*50000000000000^3165 ≤ 22210821342757^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416765349 10000000000 22210821342757 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2445473597/10000000000 : ℝ)^4189 ≤ (3876276401203/25000000000000 : ℝ)^3165 := by
    have hnat : (2445473597 : ℕ)^4189*25000000000000^3165 ≤ 3876276401203^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445473597 10000000000 3876276401203 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2505570839/5000000000 : ℝ)^4189 ≤ (40073251699519/100000000000000 : ℝ)^3165 := by
    have hnat : (2505570839 : ℕ)^4189*100000000000000^3165 ≤ 40073251699519^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505570839 5000000000 40073251699519 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416765349/10000000000 : ℝ), (-2445473597/10000000000 : ℝ), (2505570839/5000000000 : ℝ)] ![(22210821342757/50000000000000 : ℝ), (3876276401203/25000000000000 : ℝ), (40073251699519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416765349/10000000000 : ℝ)|^4189 ≤ (22210821342757/50000000000000 : ℝ)^3165
        have hw : |(5416765349/10000000000 : ℝ)|=(5416765349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2445473597/10000000000 : ℝ)|^4189 ≤ (3876276401203/25000000000000 : ℝ)^3165
        have hw : |(-2445473597/10000000000 : ℝ)|=(2445473597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2505570839/5000000000 : ℝ)|^4189 ≤ (40073251699519/100000000000000 : ℝ)^3165
        have hw : |(2505570839/5000000000 : ℝ)|=(2505570839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s1_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5416764503/10000000000 : ℝ)*x 0 + (1002228449/2000000000 : ℝ)*x 1 + (-305684247/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416764503/10000000000 : ℝ)^4189 ≤ (44421633503/100000000000 : ℝ)^3165 := by
    have hnat : (5416764503 : ℕ)^4189*100000000000^3165 ≤ 44421633503^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416764503 10000000000 44421633503 100000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002228449/2000000000 : ℝ)^4189 ≤ (40073257700713/100000000000000 : ℝ)^3165 := by
    have hnat : (1002228449 : ℕ)^4189*100000000000000^3165 ≤ 40073257700713^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002228449 2000000000 40073257700713 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305684247/1250000000 : ℝ)^4189 ≤ (3101021757051/20000000000000 : ℝ)^3165 := by
    have hnat : (305684247 : ℕ)^4189*20000000000000^3165 ≤ 3101021757051^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305684247 1250000000 3101021757051 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416764503/10000000000 : ℝ), (1002228449/2000000000 : ℝ), (-305684247/1250000000 : ℝ)] ![(44421633503/100000000000 : ℝ), (40073257700713/100000000000000 : ℝ), (3101021757051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416764503/10000000000 : ℝ)|^4189 ≤ (44421633503/100000000000 : ℝ)^3165
        have hw : |(5416764503/10000000000 : ℝ)|=(5416764503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002228449/2000000000 : ℝ)|^4189 ≤ (40073257700713/100000000000000 : ℝ)^3165
        have hw : |(1002228449/2000000000 : ℝ)|=(1002228449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-305684247/1250000000 : ℝ)|^4189 ≤ (3101021757051/20000000000000 : ℝ)^3165
        have hw : |(-305684247/1250000000 : ℝ)|=(305684247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s1_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313773339/10000000000 : ℝ)*x 0 + (1842523509/5000000000 : ℝ)*x 1 + (1009471361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313773339/10000000000 : ℝ)^4189 ≤ (1314557309223/4000000000000 : ℝ)^3165 := by
    have hnat : (4313773339 : ℕ)^4189*4000000000000^3165 ≤ 1314557309223^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313773339 10000000000 1314557309223 4000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842523509/5000000000 : ℝ)^4189 ≤ (2667906309527/10000000000000 : ℝ)^3165 := by
    have hnat : (1842523509 : ℕ)^4189*10000000000000^3165 ≤ 2667906309527^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842523509 5000000000 2667906309527 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009471361/2000000000 : ℝ)^4189 ≤ (10114251039761/25000000000000 : ℝ)^3165 := by
    have hnat : (1009471361 : ℕ)^4189*25000000000000^3165 ≤ 10114251039761^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009471361 2000000000 10114251039761 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313773339/10000000000 : ℝ), (1842523509/5000000000 : ℝ), (1009471361/2000000000 : ℝ)] ![(1314557309223/4000000000000 : ℝ), (2667906309527/10000000000000 : ℝ), (10114251039761/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313773339/10000000000 : ℝ)|^4189 ≤ (1314557309223/4000000000000 : ℝ)^3165
        have hw : |(4313773339/10000000000 : ℝ)|=(4313773339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1842523509/5000000000 : ℝ)|^4189 ≤ (2667906309527/10000000000000 : ℝ)^3165
        have hw : |(1842523509/5000000000 : ℝ)|=(1842523509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009471361/2000000000 : ℝ)|^4189 ≤ (10114251039761/25000000000000 : ℝ)^3165
        have hw : |(1009471361/2000000000 : ℝ)|=(1009471361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s1_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080577073/10000000000 : ℝ)*x 0 + (5020261653/10000000000 : ℝ)*x 1 + (1420217483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080577073/10000000000 : ℝ)^4189 ≤ (12519583500563/100000000000000 : ℝ)^3165 := by
    have hnat : (2080577073 : ℕ)^4189*100000000000000^3165 ≤ 12519583500563^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080577073 10000000000 12519583500563 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5020261653/10000000000 : ℝ)^4189 ≤ (10042451742573/25000000000000 : ℝ)^3165 := by
    have hnat : (5020261653 : ℕ)^4189*25000000000000^3165 ≤ 10042451742573^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020261653 10000000000 10042451742573 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1420217483/2500000000 : ℝ)^4189 ≤ (47310609518507/100000000000000 : ℝ)^3165 := by
    have hnat : (1420217483 : ℕ)^4189*100000000000000^3165 ≤ 47310609518507^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420217483 2500000000 47310609518507 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080577073/10000000000 : ℝ), (5020261653/10000000000 : ℝ), (1420217483/2500000000 : ℝ)] ![(12519583500563/100000000000000 : ℝ), (10042451742573/25000000000000 : ℝ), (47310609518507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080577073/10000000000 : ℝ)|^4189 ≤ (12519583500563/100000000000000 : ℝ)^3165
        have hw : |(-2080577073/10000000000 : ℝ)|=(2080577073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5020261653/10000000000 : ℝ)|^4189 ≤ (10042451742573/25000000000000 : ℝ)^3165
        have hw : |(5020261653/10000000000 : ℝ)|=(5020261653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1420217483/2500000000 : ℝ)|^4189 ≤ (47310609518507/100000000000000 : ℝ)^3165
        have hw : |(1420217483/2500000000 : ℝ)|=(1420217483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s1_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1310576099/2500000000 : ℝ)*x 0 + (-1775744213/10000000000 : ℝ)*x 1 + (5680871293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310576099/2500000000 : ℝ)^4189 ≤ (21268988003689/50000000000000 : ℝ)^3165 := by
    have hnat : (1310576099 : ℕ)^4189*50000000000000^3165 ≤ 21268988003689^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310576099 2500000000 21268988003689 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1775744213/10000000000 : ℝ)^4189 ≤ (2537849864361/25000000000000 : ℝ)^3165 := by
    have hnat : (1775744213 : ℕ)^4189*25000000000000^3165 ≤ 2537849864361^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775744213 10000000000 2537849864361 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5680871293/10000000000 : ℝ)^4189 ≤ (23655312260069/50000000000000 : ℝ)^3165 := by
    have hnat : (5680871293 : ℕ)^4189*50000000000000^3165 ≤ 23655312260069^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680871293 10000000000 23655312260069 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310576099/2500000000 : ℝ), (-1775744213/10000000000 : ℝ), (5680871293/10000000000 : ℝ)] ![(21268988003689/50000000000000 : ℝ), (2537849864361/25000000000000 : ℝ), (23655312260069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310576099/2500000000 : ℝ)|^4189 ≤ (21268988003689/50000000000000 : ℝ)^3165
        have hw : |(1310576099/2500000000 : ℝ)|=(1310576099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1775744213/10000000000 : ℝ)|^4189 ≤ (2537849864361/25000000000000 : ℝ)^3165
        have hw : |(-1775744213/10000000000 : ℝ)|=(1775744213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5680871293/10000000000 : ℝ)|^4189 ≤ (23655312260069/50000000000000 : ℝ)^3165
        have hw : |(5680871293/10000000000 : ℝ)|=(5680871293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s1_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40955501/78125000 : ℝ)*x 0 + (284043607/500000000 : ℝ)*x 1 + (-1775743359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40955501/78125000 : ℝ)^4189 ≤ (5317246641143/12500000000000 : ℝ)^3165 := by
    have hnat : (40955501 : ℕ)^4189*12500000000000^3165 ≤ 5317246641143^3165*78125000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40955501 78125000 5317246641143 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284043607/500000000 : ℝ)^4189 ≤ (47310633856201/100000000000000 : ℝ)^3165 := by
    have hnat : (284043607 : ℕ)^4189*100000000000000^3165 ≤ 47310633856201^3165*500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284043607 500000000 47310633856201 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1775743359/10000000000 : ℝ)^4189 ≤ (2030278599169/20000000000000 : ℝ)^3165 := by
    have hnat : (1775743359 : ℕ)^4189*20000000000000^3165 ≤ 2030278599169^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775743359 10000000000 2030278599169 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40955501/78125000 : ℝ), (284043607/500000000 : ℝ), (-1775743359/10000000000 : ℝ)] ![(5317246641143/12500000000000 : ℝ), (47310633856201/100000000000000 : ℝ), (2030278599169/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40955501/78125000 : ℝ)|^4189 ≤ (5317246641143/12500000000000 : ℝ)^3165
        have hw : |(40955501/78125000 : ℝ)|=(40955501/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284043607/500000000 : ℝ)|^4189 ≤ (47310633856201/100000000000000 : ℝ)^3165
        have hw : |(284043607/500000000 : ℝ)|=(284043607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1775743359/10000000000 : ℝ)|^4189 ≤ (2030278599169/20000000000000 : ℝ)^3165
        have hw : |(-1775743359/10000000000 : ℝ)|=(1775743359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s1_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4315272719/10000000000 : ℝ)*x 0 + (5029059807/10000000000 : ℝ)*x 1 + (1851849663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315272719/10000000000 : ℝ)^4189 ≤ (32879052145559/100000000000000 : ℝ)^3165 := by
    have hnat : (4315272719 : ℕ)^4189*100000000000000^3165 ≤ 32879052145559^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315272719 10000000000 32879052145559 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5029059807/10000000000 : ℝ)^4189 ≤ (20131504423371/50000000000000 : ℝ)^3165 := by
    have hnat : (5029059807 : ℕ)^4189*50000000000000^3165 ≤ 20131504423371^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5029059807 10000000000 20131504423371 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1851849663/5000000000 : ℝ)^4189 ≤ (5371587798203/20000000000000 : ℝ)^3165 := by
    have hnat : (1851849663 : ℕ)^4189*20000000000000^3165 ≤ 5371587798203^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851849663 5000000000 5371587798203 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315272719/10000000000 : ℝ), (5029059807/10000000000 : ℝ), (1851849663/5000000000 : ℝ)] ![(32879052145559/100000000000000 : ℝ), (20131504423371/50000000000000 : ℝ), (5371587798203/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315272719/10000000000 : ℝ)|^4189 ≤ (32879052145559/100000000000000 : ℝ)^3165
        have hw : |(4315272719/10000000000 : ℝ)|=(4315272719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5029059807/10000000000 : ℝ)|^4189 ≤ (20131504423371/50000000000000 : ℝ)^3165
        have hw : |(5029059807/10000000000 : ℝ)|=(5029059807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1851849663/5000000000 : ℝ)|^4189 ≤ (5371587798203/20000000000000 : ℝ)^3165
        have hw : |(1851849663/5000000000 : ℝ)|=(1851849663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27651/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (589/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5887/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4049/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27651/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (589/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27651/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (589/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27651/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (589/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27651/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (589/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27651/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (589/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27651/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (589/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (589/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (75688720609/100000000000000000000 : ℝ) := by
    have hpowers : (589/100000 : ℝ)^8377 ≤ (75688720609/100000000000000000000 : ℝ)^2048 := by
      have hnat : (589 : ℕ)^8377*100000000000000000000^2048 ≤ 75688720609^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 100000 75688720609 100000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/100000 : ℝ)) (X := (75688720609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27651/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (520489502895266651/100000000000000000000 : ℝ) := by
    have hpowers : (27651/100000 : ℝ)^8377 ≤ (520489502895266651/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27651 : ℕ)^8377*100000000000000000000^2048 ≤ 520489502895266651^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27651 100000 520489502895266651 100000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27651/100000 : ℝ)) (X := (520489502895266651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000075688720609/50000000000000000000 : ℝ) ≤ (500000000185043/500000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (50000000075688720609/50000000000000000000 : ℝ)^2048 ≤ (500000000185043/500000000000000 : ℝ)^8377 := by
      have hnat : (50000000075688720609 : ℕ)^2048*500000000000000^8377 ≤ 500000000185043^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000075688720609 50000000000000000000 500000000185043 500000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000185043/500000000000000 : ℝ)) (X := (50000000075688720609/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5026024478929199363/5000000000000000000 : ℝ) ≤ (2503174982444481/2500000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (5026024478929199363/5000000000000000000 : ℝ)^2048 ≤ (2503174982444481/2500000000000000 : ℝ)^8377 := by
      have hnat : (5026024478929199363 : ℕ)^2048*2500000000000000^8377 ≤ 2503174982444481^8377*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5026024478929199363 5000000000000000000 2503174982444481 2500000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503174982444481/2500000000000000 : ℝ)) (X := (5026024478929199363/5000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50520489502895266651/50000000000000000000 : ℝ) ≤ (2506349963963747/2500000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (50520489502895266651/50000000000000000000 : ℝ)^2048 ≤ (2506349963963747/2500000000000000 : ℝ)^8377 := by
      have hnat : (50520489502895266651 : ℕ)^2048*2500000000000000^8377 ≤ 2506349963963747^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50520489502895266651 50000000000000000000 2506349963963747 2500000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506349963963747/2500000000000000 : ℝ)) (X := (50520489502895266651/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(75688720609/100000000000000000000 : ℝ) ≤ ((33825629948404236491/33827500000000000000 : ℝ)+2*(1587490759633/338275000000000 : ℝ)*(589/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (33825629948404236491/33827500000000000000 : ℝ)+2*(1587490759633/338275000000000 : ℝ)*(589/100000 : ℝ)=(500000000185043/500000000000000 : ℝ) by norm_num, show 1+2*(75688720609/100000000000000000000 : ℝ)=(50000000075688720609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(520489502895266651/100000000000000000000 : ℝ)+(75688720609/100000000000000000000 : ℝ) ≤ ((33825629948404236491/33827500000000000000 : ℝ)+(1587490759633/338275000000000 : ℝ)*((27651/100000 : ℝ)+(589/100000 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (33825629948404236491/33827500000000000000 : ℝ)+(1587490759633/338275000000000 : ℝ)*((27651/100000 : ℝ)+(589/100000 : ℝ))=(2503174982444481/2500000000000000 : ℝ) by norm_num, show 1+(520489502895266651/100000000000000000000 : ℝ)+(75688720609/100000000000000000000 : ℝ)=(5026024478929199363/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(520489502895266651/100000000000000000000 : ℝ) ≤ ((33825629948404236491/33827500000000000000 : ℝ)+2*(1587490759633/338275000000000 : ℝ)*(27651/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (33825629948404236491/33827500000000000000 : ℝ)+2*(1587490759633/338275000000000 : ℝ)*(27651/100000 : ℝ)=(2506349963963747/2500000000000000 : ℝ) by norm_num, show 1+2*(520489502895266651/100000000000000000000 : ℝ)=(50520489502895266651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33825629948404236491/33827500000000000000 : ℝ)*(X 1 0+X 2 0)+(1587490759633/338275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (589/100000 : ℝ)) (hi := (27651/100000 : ℝ)) (c := (33825629948404236491/33827500000000000000 : ℝ)) (alpha := (1587490759633/338275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33825629948404236491/33827500000000000000 : ℝ)*(X 0 1+X 2 1)+(1587490759633/338275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (589/100000 : ℝ)) (hi := (27651/100000 : ℝ)) (c := (33825629948404236491/33827500000000000000 : ℝ)) (alpha := (1587490759633/338275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33825629948404236491/33827500000000000000 : ℝ)*(X 0 2+X 1 2)+(1587490759633/338275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (589/100000 : ℝ)) (hi := (27651/100000 : ℝ)) (c := (33825629948404236491/33827500000000000000 : ℝ)) (alpha := (1587490759633/338275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2079828557/10000000000 : ℝ)*X 0 0+(569016833/1000000000 : ℝ)*X 0 1+(15659817/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416765349/10000000000 : ℝ)*X 1 0+(-2445473597/10000000000 : ℝ)*X 1 1+(2505570839/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5416764503/10000000000 : ℝ)*X 2 0+(1002228449/2000000000 : ℝ)*X 2 1+(-305684247/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313773339/10000000000 : ℝ)*X 0 0+(1842523509/5000000000 : ℝ)*X 0 1+(1009471361/2000000000 : ℝ)*X 0 2+(4313773339/10000000000 : ℝ)*X 1 0+(1842523509/5000000000 : ℝ)*X 1 1+(1009471361/2000000000 : ℝ)*X 1 2+(4313773339/10000000000 : ℝ)*X 2 0+(1842523509/5000000000 : ℝ)*X 2 1+(1009471361/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2080577073/10000000000 : ℝ)*X 0 0+(5020261653/10000000000 : ℝ)*X 0 1+(1420217483/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1310576099/2500000000 : ℝ)*X 1 0+(-1775744213/10000000000 : ℝ)*X 1 1+(5680871293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((40955501/78125000 : ℝ)*X 2 0+(284043607/500000000 : ℝ)*X 2 1+(-1775743359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315272719/10000000000 : ℝ)*X 0 0+(5029059807/10000000000 : ℝ)*X 0 1+(1851849663/5000000000 : ℝ)*X 0 2+(4315272719/10000000000 : ℝ)*X 1 0+(5029059807/10000000000 : ℝ)*X 1 1+(1851849663/5000000000 : ℝ)*X 1 2+(4315272719/10000000000 : ℝ)*X 2 0+(5029059807/10000000000 : ℝ)*X 2 1+(1851849663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1528641284544074475166308033/422843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (981841901/100000000000000 : ℝ)*(base19) + (738528941/100000000000000 : ℝ)*(base23) + (2637863/1250000000000 : ℝ)*(upper3) + (720593/10000000000000 : ℝ)*(upper4) + (507909/25000000000000 : ℝ)*(upper5) + (275845130478907/25000000000000 : ℝ)*(major0) + (275845130478907/25000000000000 : ℝ)*(major1) + (275845130478907/25000000000000 : ℝ)*(major2) + (368175701734667/25000000000000 : ℝ)*(sp0) + (46022078478139/3125000000000 : ℝ)*(sp1) + (1472706754613409/100000000000000 : ℝ)*(sp2) + (367025020515967/50000000000000 : ℝ)*(sp3) + (2343101841/50000000000000 : ℝ)*(sp4) + (677830429/20000000000000 : ℝ)*(sp7) + (367026715092039/50000000000000 : ℝ)*(f.failure) + (29454149862847/2000000000000 : ℝ)*(f.sum) + (220499515632349/67655000000000000000000000000 : ℝ)*base66 + (10664554425090642163/845687500000000000000000000000000 : ℝ)*base68 + (9144394839321954663/845687500000000000000000000000000 : ℝ)*base70 + (4659679817916892163/845687500000000000000000000000000 : ℝ)*base72 + (584092528856909/67655000000000000000000000000 : ℝ)*base74 + (2292787107209454663/845687500000000000000000000000000 : ℝ)*base76 + (6101107120299704663/845687500000000000000000000000000 : ℝ)*base78 + (7861415312683704663/845687500000000000000000000000000 : ℝ)*base80 + (82706231450021/16913750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (340909/250000000000000000000 : ℝ)*base90 + (340909/250000000000000000000 : ℝ)*base92 + (340909/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (216160837064927606005791279/67655000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (771079917/50000000000000 : ℝ)*(base19) + (246251313/12500000000000 : ℝ)*(base23) + (37596777/20000000000000 : ℝ)*(upper2) + (330370773/100000000000000 : ℝ)*(upper3) + (159025229/100000000000000 : ℝ)*(upper5) + (45365318980823/4000000000000 : ℝ)*(major0) + (45365318980823/4000000000000 : ℝ)*(major1) + (45365318980823/4000000000000 : ℝ)*(major2) + (8088783147/100000000000000 : ℝ)*(sp1) + (12495369373/100000000000000 : ℝ)*(sp2) + (94609595000217/6250000000000 : ℝ)*(sp4) + (151374388906049/10000000000000 : ℝ)*(sp5) + (302747810924719/20000000000000 : ℝ)*(sp6) + (754512322536141/100000000000000 : ℝ)*(sp7) + (754512322536141/100000000000000 : ℝ)*(f.failure) + (94609595000217/6250000000000 : ℝ)*(f.sum) + (3728331038933/13531000000000000000000000000 : ℝ)*base66 + (389113880664217907/135310000000000000000000000000000 : ℝ)*base68 + (776668899977987907/135310000000000000000000000000000 : ℝ)*base70 + (104783759247892093/135310000000000000000000000000000 : ℝ)*base71 + (19530447057109/6765500000000000000000000000 : ℝ)*base74 + (306242693999092093/135310000000000000000000000000000 : ℝ)*base75 + (140503426237267907/135310000000000000000000000000000 : ℝ)*base78 + (664218929384607907/135310000000000000000000000000000 : ℝ)*base80 + (49222372764023/13531000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1293329/500000000000000000000 : ℝ)*base89 + (1293329/500000000000000000000 : ℝ)*base91 + (1293329/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1185_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27651/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (589/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5887/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4049/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1185_s2_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130782749/10000000000 : ℝ)*x 0 + (1375703571/2500000000 : ℝ)*x 1 + (1291513463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130782749/10000000000 : ℝ)^4189 ≤ (2584196900497/20000000000000 : ℝ)^3165 := by
    have hnat : (2130782749 : ℕ)^4189*20000000000000^3165 ≤ 2584196900497^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130782749 10000000000 2584196900497 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375703571/2500000000 : ℝ)^4189 ≤ (9071602498181/20000000000000 : ℝ)^3165 := by
    have hnat : (1375703571 : ℕ)^4189*20000000000000^3165 ≤ 9071602498181^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375703571 2500000000 9071602498181 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291513463/2500000000 : ℝ)^4189 ≤ (41721002991667/100000000000000 : ℝ)^3165 := by
    have hnat : (1291513463 : ℕ)^4189*100000000000000^3165 ≤ 41721002991667^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291513463 2500000000 41721002991667 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130782749/10000000000 : ℝ), (1375703571/2500000000 : ℝ), (1291513463/2500000000 : ℝ)] ![(2584196900497/20000000000000 : ℝ), (9071602498181/20000000000000 : ℝ), (41721002991667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130782749/10000000000 : ℝ)|^4189 ≤ (2584196900497/20000000000000 : ℝ)^3165
        have hw : |(-2130782749/10000000000 : ℝ)|=(2130782749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375703571/2500000000 : ℝ)|^4189 ≤ (9071602498181/20000000000000 : ℝ)^3165
        have hw : |(1375703571/2500000000 : ℝ)|=(1375703571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291513463/2500000000 : ℝ)|^4189 ≤ (41721002991667/100000000000000 : ℝ)^3165
        have hw : |(1291513463/2500000000 : ℝ)|=(1291513463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s2_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686018571/5000000000 : ℝ)*x 0 + (-576394223/2500000000 : ℝ)*x 1 + (516605757/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686018571/5000000000 : ℝ)^4189 ≤ (5492101356381/12500000000000 : ℝ)^3165 := by
    have hnat : (2686018571 : ℕ)^4189*12500000000000^3165 ≤ 5492101356381^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686018571 5000000000 5492101356381 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576394223/2500000000 : ℝ)^4189 ≤ (448192075101/3125000000000 : ℝ)^3165 := by
    have hnat : (576394223 : ℕ)^4189*3125000000000^3165 ≤ 448192075101^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576394223 2500000000 448192075101 3125000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516605757/1000000000 : ℝ)^4189 ≤ (41721042732951/100000000000000 : ℝ)^3165 := by
    have hnat : (516605757 : ℕ)^4189*100000000000000^3165 ≤ 41721042732951^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516605757 1000000000 41721042732951 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686018571/5000000000 : ℝ), (-576394223/2500000000 : ℝ), (516605757/1000000000 : ℝ)] ![(5492101356381/12500000000000 : ℝ), (448192075101/3125000000000 : ℝ), (41721042732951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686018571/5000000000 : ℝ)|^4189 ≤ (5492101356381/12500000000000 : ℝ)^3165
        have hw : |(2686018571/5000000000 : ℝ)|=(2686018571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-576394223/2500000000 : ℝ)|^4189 ≤ (448192075101/3125000000000 : ℝ)^3165
        have hw : |(-576394223/2500000000 : ℝ)|=(576394223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516605757/1000000000 : ℝ)|^4189 ≤ (41721042732951/100000000000000 : ℝ)^3165
        have hw : |(516605757/1000000000 : ℝ)|=(516605757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s2_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372038497/10000000000 : ℝ)*x 0 + (1291513909/2500000000 : ℝ)*x 1 + (-2305577621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372038497/10000000000 : ℝ)^4189 ≤ (8787365103773/20000000000000 : ℝ)^3165 := by
    have hnat : (5372038497 : ℕ)^4189*20000000000000^3165 ≤ 8787365103773^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372038497 10000000000 8787365103773 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291513909/2500000000 : ℝ)^4189 ≤ (41721022060641/100000000000000 : ℝ)^3165 := by
    have hnat : (1291513909 : ℕ)^4189*100000000000000^3165 ≤ 41721022060641^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291513909 2500000000 41721022060641 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2305577621/10000000000 : ℝ)^4189 ≤ (1434215240527/10000000000000 : ℝ)^3165 := by
    have hnat : (2305577621 : ℕ)^4189*10000000000000^3165 ≤ 1434215240527^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305577621 10000000000 1434215240527 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372038497/10000000000 : ℝ), (1291513909/2500000000 : ℝ), (-2305577621/10000000000 : ℝ)] ![(8787365103773/20000000000000 : ℝ), (41721022060641/100000000000000 : ℝ), (1434215240527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372038497/10000000000 : ℝ)|^4189 ≤ (8787365103773/20000000000000 : ℝ)^3165
        have hw : |(5372038497/10000000000 : ℝ)|=(5372038497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1291513909/2500000000 : ℝ)|^4189 ≤ (41721022060641/100000000000000 : ℝ)^3165
        have hw : |(1291513909/2500000000 : ℝ)|=(1291513909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2305577621/10000000000 : ℝ)|^4189 ≤ (1434215240527/10000000000000 : ℝ)^3165
        have hw : |(-2305577621/10000000000 : ℝ)|=(2305577621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s2_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4348836837/10000000000 : ℝ)*x 0 + (4023898041/10000000000 : ℝ)*x 1 + (234976259/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348836837/10000000000 : ℝ)^4189 ≤ (16608974709723/50000000000000 : ℝ)^3165 := by
    have hnat : (4348836837 : ℕ)^4189*50000000000000^3165 ≤ 16608974709723^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348836837 10000000000 16608974709723 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023898041/10000000000 : ℝ)^4189 ≤ (29973327570727/100000000000000 : ℝ)^3165 := by
    have hnat : (4023898041 : ℕ)^4189*100000000000000^3165 ≤ 29973327570727^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023898041 10000000000 29973327570727 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234976259/500000000 : ℝ)^4189 ≤ (36808722991813/100000000000000 : ℝ)^3165 := by
    have hnat : (234976259 : ℕ)^4189*100000000000000^3165 ≤ 36808722991813^3165*500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234976259 500000000 36808722991813 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348836837/10000000000 : ℝ), (4023898041/10000000000 : ℝ), (234976259/500000000 : ℝ)] ![(16608974709723/50000000000000 : ℝ), (29973327570727/100000000000000 : ℝ), (36808722991813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348836837/10000000000 : ℝ)|^4189 ≤ (16608974709723/50000000000000 : ℝ)^3165
        have hw : |(4348836837/10000000000 : ℝ)|=(4348836837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023898041/10000000000 : ℝ)|^4189 ≤ (29973327570727/100000000000000 : ℝ)^3165
        have hw : |(4023898041/10000000000 : ℝ)|=(4023898041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(234976259/500000000 : ℝ)|^4189 ≤ (36808722991813/100000000000000 : ℝ)^3165
        have hw : |(234976259/500000000 : ℝ)|=(234976259/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s2_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130873179/10000000000 : ℝ)*x 0 + (646038501/1250000000 : ℝ)*x 1 + (5500538881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130873179/10000000000 : ℝ)^4189 ≤ (6460855144247/50000000000000 : ℝ)^3165 := by
    have hnat : (2130873179 : ℕ)^4189*50000000000000^3165 ≤ 6460855144247^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130873179 10000000000 6460855144247 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (646038501/1250000000 : ℝ)^4189 ≤ (4174509910943/10000000000000 : ℝ)^3165 := by
    have hnat : (646038501 : ℕ)^4189*10000000000000^3165 ≤ 4174509910943^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646038501 1250000000 4174509910943 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500538881/10000000000 : ℝ)^4189 ≤ (5666648823457/12500000000000 : ℝ)^3165 := by
    have hnat : (5500538881 : ℕ)^4189*12500000000000^3165 ≤ 5666648823457^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500538881 10000000000 5666648823457 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130873179/10000000000 : ℝ), (646038501/1250000000 : ℝ), (5500538881/10000000000 : ℝ)] ![(6460855144247/50000000000000 : ℝ), (4174509910943/10000000000000 : ℝ), (5666648823457/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130873179/10000000000 : ℝ)|^4189 ≤ (6460855144247/50000000000000 : ℝ)^3165
        have hw : |(-2130873179/10000000000 : ℝ)|=(2130873179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(646038501/1250000000 : ℝ)|^4189 ≤ (4174509910943/10000000000000 : ℝ)^3165
        have hw : |(646038501/1250000000 : ℝ)|=(646038501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500538881/10000000000 : ℝ)|^4189 ≤ (5666648823457/12500000000000 : ℝ)^3165
        have hw : |(5500538881/10000000000 : ℝ)|=(5500538881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s2_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528635051/1000000000 : ℝ)*x 0 + (-985547043/5000000000 : ℝ)*x 1 + (550053889/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528635051/1000000000 : ℝ)^4189 ≤ (2150582940009/5000000000000 : ℝ)^3165 := by
    have hnat : (528635051 : ℕ)^4189*5000000000000^3165 ≤ 2150582940009^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528635051 1000000000 2150582940009 5000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985547043/5000000000 : ℝ)^4189 ≤ (11655150508801/100000000000000 : ℝ)^3165 := by
    have hnat : (985547043 : ℕ)^4189*100000000000000^3165 ≤ 11655150508801^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985547043 5000000000 11655150508801 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550053889/1000000000 : ℝ)^4189 ≤ (11333297671457/25000000000000 : ℝ)^3165 := by
    have hnat : (550053889 : ℕ)^4189*25000000000000^3165 ≤ 11333297671457^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550053889 1000000000 11333297671457 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528635051/1000000000 : ℝ), (-985547043/5000000000 : ℝ), (550053889/1000000000 : ℝ)] ![(2150582940009/5000000000000 : ℝ), (11655150508801/100000000000000 : ℝ), (11333297671457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528635051/1000000000 : ℝ)|^4189 ≤ (2150582940009/5000000000000 : ℝ)^3165
        have hw : |(528635051/1000000000 : ℝ)|=(528635051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985547043/5000000000 : ℝ)|^4189 ≤ (11655150508801/100000000000000 : ℝ)^3165
        have hw : |(-985547043/5000000000 : ℝ)|=(985547043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550053889/1000000000 : ℝ)|^4189 ≤ (11333297671457/25000000000000 : ℝ)^3165
        have hw : |(550053889/1000000000 : ℝ)|=(550053889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s2_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660793833/1250000000 : ℝ)*x 0 + (1100107779/2000000000 : ℝ)*x 1 + (-985546933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660793833/1250000000 : ℝ)^4189 ≤ (21505830229287/50000000000000 : ℝ)^3165 := by
    have hnat : (660793833 : ℕ)^4189*50000000000000^3165 ≤ 21505830229287^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660793833 1250000000 21505830229287 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100107779/2000000000 : ℝ)^4189 ≤ (45333190740369/100000000000000 : ℝ)^3165 := by
    have hnat : (1100107779 : ℕ)^4189*100000000000000^3165 ≤ 45333190740369^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100107779 2000000000 45333190740369 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985546933/5000000000 : ℝ)^4189 ≤ (2913787196763/25000000000000 : ℝ)^3165 := by
    have hnat : (985546933 : ℕ)^4189*25000000000000^3165 ≤ 2913787196763^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985546933 5000000000 2913787196763 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660793833/1250000000 : ℝ), (1100107779/2000000000 : ℝ), (-985546933/5000000000 : ℝ)] ![(21505830229287/50000000000000 : ℝ), (45333190740369/100000000000000 : ℝ), (2913787196763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660793833/1250000000 : ℝ)|^4189 ≤ (21505830229287/50000000000000 : ℝ)^3165
        have hw : |(660793833/1250000000 : ℝ)|=(660793833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100107779/2000000000 : ℝ)|^4189 ≤ (45333190740369/100000000000000 : ℝ)^3165
        have hw : |(1100107779/2000000000 : ℝ)|=(1100107779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-985546933/5000000000 : ℝ)|^4189 ≤ (2913787196763/25000000000000 : ℝ)^3165
        have hw : |(-985546933/5000000000 : ℝ)|=(985546933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s2_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43490203/100000000 : ℝ)*x 0 + (2347502691/5000000000 : ℝ)*x 1 + (2014230447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43490203/100000000 : ℝ)^4189 ≤ (3321980417981/10000000000000 : ℝ)^3165 := by
    have hnat : (43490203 : ℕ)^4189*10000000000000^3165 ≤ 3321980417981^3165*100000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43490203 100000000 3321980417981 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2347502691/5000000000 : ℝ)^4189 ≤ (735237513217/2000000000000 : ℝ)^3165 := by
    have hnat : (2347502691 : ℕ)^4189*2000000000000^3165 ≤ 735237513217^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347502691 5000000000 735237513217 2000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014230447/5000000000 : ℝ)^4189 ≤ (7504580033949/25000000000000 : ℝ)^3165 := by
    have hnat : (2014230447 : ℕ)^4189*25000000000000^3165 ≤ 7504580033949^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014230447 5000000000 7504580033949 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43490203/100000000 : ℝ), (2347502691/5000000000 : ℝ), (2014230447/5000000000 : ℝ)] ![(3321980417981/10000000000000 : ℝ), (735237513217/2000000000000 : ℝ), (7504580033949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43490203/100000000 : ℝ)|^4189 ≤ (3321980417981/10000000000000 : ℝ)^3165
        have hw : |(43490203/100000000 : ℝ)|=(43490203/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2347502691/5000000000 : ℝ)|^4189 ≤ (735237513217/2000000000000 : ℝ)^3165
        have hw : |(2347502691/5000000000 : ℝ)|=(2347502691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014230447/5000000000 : ℝ)|^4189 ≤ (7504580033949/25000000000000 : ℝ)^3165
        have hw : |(2014230447/5000000000 : ℝ)|=(2014230447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4049/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5887/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (463/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8189/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4049/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5887/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4049/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5887/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4049/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5887/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4049/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5887/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4049/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5887/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4049/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5887/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5887/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (929946946720239/100000000000000000000 : ℝ) := by
    have hpowers : (5887/100000 : ℝ)^8377 ≤ (929946946720239/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5887 : ℕ)^8377*100000000000000000000^2048 ≤ 929946946720239^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5887 100000 929946946720239 100000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5887/100000 : ℝ)) (X := (929946946720239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4049/20000 : ℝ) ^ (8377/2048 : ℝ) ≤ (72707532296245491/50000000000000000000 : ℝ) := by
    have hpowers : (4049/20000 : ℝ)^8377 ≤ (72707532296245491/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4049 : ℕ)^8377*50000000000000000000^2048 ≤ 72707532296245491^2048*20000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4049 20000 72707532296245491 50000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4049/20000 : ℝ)) (X := (72707532296245491/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000929946946720239/50000000000000000000 : ℝ) ≤ (625002841885469/625000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (50000929946946720239/50000000000000000000 : ℝ)^2048 ≤ (625002841885469/625000000000000 : ℝ)^8377 := by
      have hnat : (50000929946946720239 : ℕ)^2048*625000000000000^8377 ≤ 625002841885469^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000929946946720239 50000000000000000000 625002841885469 625000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625002841885469/625000000000000 : ℝ)) (X := (50000929946946720239/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100146345011539211221/100000000000000000000 : ℝ) ≤ (10003575850937831/10000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (100146345011539211221/100000000000000000000 : ℝ)^2048 ≤ (10003575850937831/10000000000000000 : ℝ)^8377 := by
      have hnat : (100146345011539211221 : ℕ)^2048*10000000000000000^8377 ≤ 10003575850937831^8377*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100146345011539211221 100000000000000000000 10003575850937831 10000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003575850937831/10000000000000000 : ℝ)) (X := (100146345011539211221/100000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25072707532296245491/25000000000000000000 : ℝ) ≤ (5003553115854079/5000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (25072707532296245491/25000000000000000000 : ℝ)^2048 ≤ (5003553115854079/5000000000000000 : ℝ)^8377 := by
      have hnat : (25072707532296245491 : ℕ)^2048*5000000000000000^8377 ≤ 5003553115854079^8377*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25072707532296245491 25000000000000000000 5003553115854079 5000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003553115854079/5000000000000000 : ℝ)) (X := (25072707532296245491/25000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(929946946720239/100000000000000000000 : ℝ) ≤ ((23923181026245865389/23930000000000000000 : ℝ)+2*(1176793590109/478600000000000 : ℝ)*(5887/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (23923181026245865389/23930000000000000000 : ℝ)+2*(1176793590109/478600000000000 : ℝ)*(5887/100000 : ℝ)=(625002841885469/625000000000000 : ℝ) by norm_num, show 1+2*(929946946720239/100000000000000000000 : ℝ)=(50000929946946720239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(72707532296245491/50000000000000000000 : ℝ)+(929946946720239/100000000000000000000 : ℝ) ≤ ((23923181026245865389/23930000000000000000 : ℝ)+(1176793590109/478600000000000 : ℝ)*((4049/20000 : ℝ)+(5887/100000 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (23923181026245865389/23930000000000000000 : ℝ)+(1176793590109/478600000000000 : ℝ)*((4049/20000 : ℝ)+(5887/100000 : ℝ))=(10003575850937831/10000000000000000 : ℝ) by norm_num, show 1+(72707532296245491/50000000000000000000 : ℝ)+(929946946720239/100000000000000000000 : ℝ)=(100146345011539211221/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(72707532296245491/50000000000000000000 : ℝ) ≤ ((23923181026245865389/23930000000000000000 : ℝ)+2*(1176793590109/478600000000000 : ℝ)*(4049/20000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (23923181026245865389/23930000000000000000 : ℝ)+2*(1176793590109/478600000000000 : ℝ)*(4049/20000 : ℝ)=(5003553115854079/5000000000000000 : ℝ) by norm_num, show 1+2*(72707532296245491/50000000000000000000 : ℝ)=(25072707532296245491/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23923181026245865389/23930000000000000000 : ℝ)*(X 1 0+X 2 0)+(1176793590109/478600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (5887/100000 : ℝ)) (hi := (4049/20000 : ℝ)) (c := (23923181026245865389/23930000000000000000 : ℝ)) (alpha := (1176793590109/478600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23923181026245865389/23930000000000000000 : ℝ)*(X 0 1+X 2 1)+(1176793590109/478600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (5887/100000 : ℝ)) (hi := (4049/20000 : ℝ)) (c := (23923181026245865389/23930000000000000000 : ℝ)) (alpha := (1176793590109/478600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23923181026245865389/23930000000000000000 : ℝ)*(X 0 2+X 1 2)+(1176793590109/478600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (5887/100000 : ℝ)) (hi := (4049/20000 : ℝ)) (c := (23923181026245865389/23930000000000000000 : ℝ)) (alpha := (1176793590109/478600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2130782749/10000000000 : ℝ)*X 0 0+(1375703571/2500000000 : ℝ)*X 0 1+(1291513463/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686018571/5000000000 : ℝ)*X 1 0+(-576394223/2500000000 : ℝ)*X 1 1+(516605757/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372038497/10000000000 : ℝ)*X 2 0+(1291513909/2500000000 : ℝ)*X 2 1+(-2305577621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348836837/10000000000 : ℝ)*X 0 0+(4023898041/10000000000 : ℝ)*X 0 1+(234976259/500000000 : ℝ)*X 0 2+(4348836837/10000000000 : ℝ)*X 1 0+(4023898041/10000000000 : ℝ)*X 1 1+(234976259/500000000 : ℝ)*X 1 2+(4348836837/10000000000 : ℝ)*X 2 0+(4023898041/10000000000 : ℝ)*X 2 1+(234976259/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2130873179/10000000000 : ℝ)*X 0 0+(646038501/1250000000 : ℝ)*X 0 1+(5500538881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528635051/1000000000 : ℝ)*X 1 0+(-985547043/5000000000 : ℝ)*X 1 1+(550053889/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660793833/1250000000 : ℝ)*X 2 0+(1100107779/2000000000 : ℝ)*X 2 1+(-985546933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43490203/100000000 : ℝ)*X 0 0+(2347502691/5000000000 : ℝ)*X 0 1+(2014230447/5000000000 : ℝ)*X 0 2+(43490203/100000000 : ℝ)*X 1 0+(2347502691/5000000000 : ℝ)*X 1 1+(2014230447/5000000000 : ℝ)*X 1 2+(43490203/100000000 : ℝ)*X 2 0+(2347502691/5000000000 : ℝ)*X 2 1+(2014230447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5923910852351823650797080837/598250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1489332193/100000000000000 : ℝ)*(base19) + (22795791/1250000000000 : ℝ)*(base23) + (15930113/50000000000000 : ℝ)*(upper2) + (317844601/50000000000000 : ℝ)*(upper3) + (254629723/100000000000000 : ℝ)*(upper4) + (2224841421805989/100000000000000 : ℝ)*(major0) + (2224841421805989/100000000000000 : ℝ)*(major1) + (2224841421805989/100000000000000 : ℝ)*(major2) + (742377917691171/25000000000000 : ℝ)*(sp0) + (371193213546929/12500000000000 : ℝ)*(sp1) + (1484772687022173/50000000000000 : ℝ)*(sp2) + (1480117023323731/100000000000000 : ℝ)*(sp3) + (35526942941/100000000000000 : ℝ)*(sp4) + (18292511751/100000000000000 : ℝ)*(sp7) + (740067657917741/50000000000000 : ℝ)*(f.failure) + (1484773598853813/50000000000000 : ℝ)*(f.sum) + (130321135542241/23930000000000000000000000000 : ℝ)*base65 + (19094525304367064721/2393000000000000000000000000000000 : ℝ)*base67 + (10312236539849064721/2393000000000000000000000000000000 : ℝ)*base69 + (26185829382745064721/2393000000000000000000000000000000 : ℝ)*base71 + (2235113772431/23930000000000000000000000000 : ℝ)*base73 + (7242332336606064721/2393000000000000000000000000000000 : ℝ)*base75 + (25915677347871064721/2393000000000000000000000000000000 : ℝ)*base77 + (8951234334528935279/2393000000000000000000000000000000 : ℝ)*base80 + (54340448948361/23930000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1916271/250000000000000000000 : ℝ)*base90 + (1916271/250000000000000000000 : ℝ)*base92 + (1916271/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1183502259902702682743439213/149562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (936240063/50000000000000 : ℝ)*(base19) + (402106517/20000000000000 : ℝ)*(base23) + (229554573/100000000000000 : ℝ)*(upper3) + (1251/25000000000000 : ℝ)*(lower4) + (33179829/20000000000000 : ℝ)*(upper5) + (281889398678639/12500000000000 : ℝ)*(major0) + (281889398678639/12500000000000 : ℝ)*(major1) + (281889398678639/12500000000000 : ℝ)*(major2) + (18406694177/100000000000000 : ℝ)*(sp1) + (4302637959/20000000000000 : ℝ)*(sp2) + (3009954364899609/100000000000000 : ℝ)*(sp4) + (1504967042862653/50000000000000 : ℝ)*(sp5) + (3009930841177229/100000000000000 : ℝ)*(sp6) + (75013787509439/5000000000000 : ℝ)*(sp7) + (75013787509439/5000000000000 : ℝ)*(f.failure) + (3009954364899609/100000000000000 : ℝ)*(f.sum) + (69481985203219/11965000000000000000000000000 : ℝ)*base65 + (132888889375724429/299125000000000000000000000000000 : ℝ)*base68 + (500149783460849429/299125000000000000000000000000000 : ℝ)*base70 + (305006371466025571/299125000000000000000000000000000 : ℝ)*base71 + (10998628964551/2991250000000000000000000000 : ℝ)*base73 + (592795586397474429/299125000000000000000000000000000 : ℝ)*base76 + (394372963345900571/299125000000000000000000000000000 : ℝ)*base77 + (488694398535599429/299125000000000000000000000000000 : ℝ)*base80 + (43605670695489/11965000000000000000000000000 : ℝ)*base81 + (100309/25000000000000000000 : ℝ)*base90 + (100309/25000000000000000000 : ℝ)*base92 + (100309/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1185_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4049/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5887/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (463/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1185_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (463/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1185_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1185_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1185_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (463/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8189/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1185_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
