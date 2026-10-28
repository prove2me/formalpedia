-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1156_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:53.389666+00:00
-- url     : https://prove2.me/submissions/8583a02e-4594-4d98-8021-7b6e54deb174

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
theorem support_rectangle_w1156_s0_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1887387681/10000000000 : ℝ)*x 0 + (6051100103/10000000000 : ℝ)*x 1 + (2391120157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1887387681/10000000000 : ℝ)^8349 ≤ (27443271091/250000000000 : ℝ)^6301 := by
    have hnat : (1887387681 : ℕ)^8349*250000000000^6301 ≤ 27443271091^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887387681 10000000000 27443271091 250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6051100103/10000000000 : ℝ)^8349 ≤ (51395422196033/100000000000000 : ℝ)^6301 := by
    have hnat : (6051100103 : ℕ)^8349*100000000000000^6301 ≤ 51395422196033^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6051100103 10000000000 51395422196033 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2391120157/5000000000 : ℝ)^8349 ≤ (37627269349973/100000000000000 : ℝ)^6301 := by
    have hnat : (2391120157 : ℕ)^8349*100000000000000^6301 ≤ 37627269349973^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391120157 5000000000 37627269349973 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1887387681/10000000000 : ℝ), (6051100103/10000000000 : ℝ), (2391120157/5000000000 : ℝ)] ![(27443271091/250000000000 : ℝ), (51395422196033/100000000000000 : ℝ), (37627269349973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1887387681/10000000000 : ℝ)|^8349 ≤ (27443271091/250000000000 : ℝ)^6301
        have hw : |(-1887387681/10000000000 : ℝ)|=(1887387681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6051100103/10000000000 : ℝ)|^8349 ≤ (51395422196033/100000000000000 : ℝ)^6301
        have hw : |(6051100103/10000000000 : ℝ)|=(6051100103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2391120157/5000000000 : ℝ)|^8349 ≤ (37627269349973/100000000000000 : ℝ)^6301
        have hw : |(2391120157/5000000000 : ℝ)|=(2391120157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s0_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516005011/10000000000 : ℝ)*x 0 + (-2615166947/10000000000 : ℝ)*x 1 + (4782240383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516005011/10000000000 : ℝ)^8349 ≤ (45461680764729/100000000000000 : ℝ)^6301 := by
    have hnat : (5516005011 : ℕ)^8349*100000000000000^6301 ≤ 45461680764729^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516005011 10000000000 45461680764729 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615166947/10000000000 : ℝ)^8349 ≤ (211388114297/1250000000000 : ℝ)^6301 := by
    have hnat : (2615166947 : ℕ)^8349*1250000000000^6301 ≤ 211388114297^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615166947 10000000000 211388114297 1250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4782240383/10000000000 : ℝ)^8349 ≤ (9406817517333/25000000000000 : ℝ)^6301 := by
    have hnat : (4782240383 : ℕ)^8349*25000000000000^6301 ≤ 9406817517333^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4782240383 10000000000 9406817517333 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516005011/10000000000 : ℝ), (-2615166947/10000000000 : ℝ), (4782240383/10000000000 : ℝ)] ![(45461680764729/100000000000000 : ℝ), (211388114297/1250000000000 : ℝ), (9406817517333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516005011/10000000000 : ℝ)|^8349 ≤ (45461680764729/100000000000000 : ℝ)^6301
        have hw : |(5516005011/10000000000 : ℝ)|=(5516005011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2615166947/10000000000 : ℝ)|^8349 ≤ (211388114297/1250000000000 : ℝ)^6301
        have hw : |(-2615166947/10000000000 : ℝ)|=(2615166947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4782240383/10000000000 : ℝ)|^8349 ≤ (9406817517333/25000000000000 : ℝ)^6301
        have hw : |(4782240383/10000000000 : ℝ)|=(4782240383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s0_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34475031/62500000 : ℝ)*x 0 + (1195560117/2500000000 : ℝ)*x 1 + (-261516691/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34475031/62500000 : ℝ)^8349 ≤ (45461680207779/100000000000000 : ℝ)^6301 := by
    have hnat : (34475031 : ℕ)^8349*100000000000000^6301 ≤ 45461680207779^6301*62500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34475031 62500000 45461680207779 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195560117/2500000000 : ℝ)^8349 ≤ (18813635477749/50000000000000 : ℝ)^6301 := by
    have hnat : (1195560117 : ℕ)^8349*50000000000000^6301 ≤ 18813635477749^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195560117 2500000000 18813635477749 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261516691/1000000000 : ℝ)^8349 ≤ (16911048826731/100000000000000 : ℝ)^6301 := by
    have hnat : (261516691 : ℕ)^8349*100000000000000^6301 ≤ 16911048826731^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261516691 1000000000 16911048826731 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34475031/62500000 : ℝ), (1195560117/2500000000 : ℝ), (-261516691/1000000000 : ℝ)] ![(45461680207779/100000000000000 : ℝ), (18813635477749/50000000000000 : ℝ), (16911048826731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34475031/62500000 : ℝ)|^8349 ≤ (45461680207779/100000000000000 : ℝ)^6301
        have hw : |(34475031/62500000 : ℝ)|=(34475031/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195560117/2500000000 : ℝ)|^8349 ≤ (18813635477749/50000000000000 : ℝ)^6301
        have hw : |(1195560117/2500000000 : ℝ)|=(1195560117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261516691/1000000000 : ℝ)|^8349 ≤ (16911048826731/100000000000000 : ℝ)^6301
        have hw : |(-261516691/1000000000 : ℝ)|=(261516691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s0_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2099930487/5000000000 : ℝ)*x 0 + (1560219381/5000000000 : ℝ)*x 1 + (5651736087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099930487/5000000000 : ℝ)^8349 ≤ (31679316111623/100000000000000 : ℝ)^6301 := by
    have hnat : (2099930487 : ℕ)^8349*100000000000000^6301 ≤ 31679316111623^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099930487 5000000000 31679316111623 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560219381/5000000000 : ℝ)^8349 ≤ (21370845644497/100000000000000 : ℝ)^6301 := by
    have hnat : (1560219381 : ℕ)^8349*100000000000000^6301 ≤ 21370845644497^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560219381 5000000000 21370845644497 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5651736087/10000000000 : ℝ)^8349 ≤ (46949838222601/100000000000000 : ℝ)^6301 := by
    have hnat : (5651736087 : ℕ)^8349*100000000000000^6301 ≤ 46949838222601^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5651736087 10000000000 46949838222601 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099930487/5000000000 : ℝ), (1560219381/5000000000 : ℝ), (5651736087/10000000000 : ℝ)] ![(31679316111623/100000000000000 : ℝ), (21370845644497/100000000000000 : ℝ), (46949838222601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099930487/5000000000 : ℝ)|^8349 ≤ (31679316111623/100000000000000 : ℝ)^6301
        have hw : |(2099930487/5000000000 : ℝ)|=(2099930487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560219381/5000000000 : ℝ)|^8349 ≤ (21370845644497/100000000000000 : ℝ)^6301
        have hw : |(1560219381/5000000000 : ℝ)|=(1560219381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5651736087/10000000000 : ℝ)|^8349 ≤ (46949838222601/100000000000000 : ℝ)^6301
        have hw : |(5651736087/10000000000 : ℝ)|=(5651736087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s0_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1892492191/10000000000 : ℝ)*x 0 + (2407483149/5000000000 : ℝ)*x 1 + (3008611243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1892492191/10000000000 : ℝ)^8349 ≤ (11016663853239/100000000000000 : ℝ)^6301 := by
    have hnat : (1892492191 : ℕ)^8349*100000000000000^6301 ≤ 11016663853239^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892492191 10000000000 11016663853239 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2407483149/5000000000 : ℝ)^8349 ≤ (9492208119053/25000000000000 : ℝ)^6301 := by
    have hnat : (2407483149 : ℕ)^8349*25000000000000^6301 ≤ 9492208119053^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2407483149 5000000000 9492208119053 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3008611243/5000000000 : ℝ)^8349 ≤ (10202900730617/20000000000000 : ℝ)^6301 := by
    have hnat : (3008611243 : ℕ)^8349*20000000000000^6301 ≤ 10202900730617^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008611243 5000000000 10202900730617 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1892492191/10000000000 : ℝ), (2407483149/5000000000 : ℝ), (3008611243/5000000000 : ℝ)] ![(11016663853239/100000000000000 : ℝ), (9492208119053/25000000000000 : ℝ), (10202900730617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1892492191/10000000000 : ℝ)|^8349 ≤ (11016663853239/100000000000000 : ℝ)^6301
        have hw : |(-1892492191/10000000000 : ℝ)|=(1892492191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2407483149/5000000000 : ℝ)|^8349 ≤ (9492208119053/25000000000000 : ℝ)^6301
        have hw : |(2407483149/5000000000 : ℝ)|=(2407483149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3008611243/5000000000 : ℝ)|^8349 ≤ (10202900730617/20000000000000 : ℝ)^6301
        have hw : |(3008611243/5000000000 : ℝ)|=(3008611243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s0_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171159339/10000000000 : ℝ)*x 0 + (-1380185059/10000000000 : ℝ)*x 1 + (6017222301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171159339/10000000000 : ℝ)^8349 ≤ (163025700101/390625000000 : ℝ)^6301 := by
    have hnat : (5171159339 : ℕ)^8349*390625000000^6301 ≤ 163025700101^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171159339 10000000000 163025700101 390625000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380185059/10000000000 : ℝ)^8349 ≤ (3625459589859/50000000000000 : ℝ)^6301 := by
    have hnat : (1380185059 : ℕ)^8349*50000000000000^6301 ≤ 3625459589859^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380185059 10000000000 3625459589859 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6017222301/10000000000 : ℝ)^8349 ≤ (12753625393713/25000000000000 : ℝ)^6301 := by
    have hnat : (6017222301 : ℕ)^8349*25000000000000^6301 ≤ 12753625393713^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017222301 10000000000 12753625393713 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171159339/10000000000 : ℝ), (-1380185059/10000000000 : ℝ), (6017222301/10000000000 : ℝ)] ![(163025700101/390625000000 : ℝ), (3625459589859/50000000000000 : ℝ), (12753625393713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171159339/10000000000 : ℝ)|^8349 ≤ (163025700101/390625000000 : ℝ)^6301
        have hw : |(5171159339/10000000000 : ℝ)|=(5171159339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1380185059/10000000000 : ℝ)|^8349 ≤ (3625459589859/50000000000000 : ℝ)^6301
        have hw : |(-1380185059/10000000000 : ℝ)|=(1380185059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6017222301/10000000000 : ℝ)|^8349 ≤ (12753625393713/25000000000000 : ℝ)^6301
        have hw : |(6017222301/10000000000 : ℝ)|=(6017222301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s0_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (129278983/250000000 : ℝ)*x 0 + (1504305591/2500000000 : ℝ)*x 1 + (-345046247/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129278983/250000000 : ℝ)^8349 ≤ (41734579022673/100000000000000 : ℝ)^6301 := by
    have hnat : (129278983 : ℕ)^8349*100000000000000^6301 ≤ 41734579022673^6301*250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129278983 250000000 41734579022673 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1504305591/2500000000 : ℝ)^8349 ≤ (25507251141287/50000000000000 : ℝ)^6301 := by
    have hnat : (1504305591 : ℕ)^8349*50000000000000^6301 ≤ 25507251141287^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504305591 2500000000 25507251141287 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345046247/2500000000 : ℝ)^8349 ≤ (1812729671369/25000000000000 : ℝ)^6301 := by
    have hnat : (345046247 : ℕ)^8349*25000000000000^6301 ≤ 1812729671369^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345046247 2500000000 1812729671369 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129278983/250000000 : ℝ), (1504305591/2500000000 : ℝ), (-345046247/2500000000 : ℝ)] ![(41734579022673/100000000000000 : ℝ), (25507251141287/50000000000000 : ℝ), (1812729671369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129278983/250000000 : ℝ)|^8349 ≤ (41734579022673/100000000000000 : ℝ)^6301
        have hw : |(129278983/250000000 : ℝ)|=(129278983/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1504305591/2500000000 : ℝ)|^8349 ≤ (25507251141287/50000000000000 : ℝ)^6301
        have hw : |(1504305591/2500000000 : ℝ)|=(1504305591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345046247/2500000000 : ℝ)|^8349 ≤ (1812729671369/25000000000000 : ℝ)^6301
        have hw : |(-345046247/2500000000 : ℝ)|=(345046247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s0_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1052511073/2500000000 : ℝ)*x 0 + (2793224839/5000000000 : ℝ)*x 1 + (3188022669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052511073/2500000000 : ℝ)^8349 ≤ (7945283622433/25000000000000 : ℝ)^6301 := by
    have hnat : (1052511073 : ℕ)^8349*25000000000000^6301 ≤ 7945283622433^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052511073 2500000000 7945283622433 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2793224839/5000000000 : ℝ)^8349 ≤ (23116284832913/50000000000000 : ℝ)^6301 := by
    have hnat : (2793224839 : ℕ)^8349*50000000000000^6301 ≤ 23116284832913^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2793224839 5000000000 23116284832913 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3188022669/10000000000 : ℝ)^8349 ≤ (439725916669/2000000000000 : ℝ)^6301 := by
    have hnat : (3188022669 : ℕ)^8349*2000000000000^6301 ≤ 439725916669^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188022669 10000000000 439725916669 2000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052511073/2500000000 : ℝ), (2793224839/5000000000 : ℝ), (3188022669/10000000000 : ℝ)] ![(7945283622433/25000000000000 : ℝ), (23116284832913/50000000000000 : ℝ), (439725916669/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052511073/2500000000 : ℝ)|^8349 ≤ (7945283622433/25000000000000 : ℝ)^6301
        have hw : |(1052511073/2500000000 : ℝ)|=(1052511073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2793224839/5000000000 : ℝ)|^8349 ≤ (23116284832913/50000000000000 : ℝ)^6301
        have hw : |(2793224839/5000000000 : ℝ)|=(2793224839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3188022669/10000000000 : ℝ)|^8349 ≤ (439725916669/2000000000000 : ℝ)^6301
        have hw : |(3188022669/10000000000 : ℝ)|=(3188022669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (471/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27761/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2087/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2087 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2087*1^512 ≤ 0^512*1^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2087/512 : ℝ) ≤ (2387416157311057803/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2087 ≤ (2387416157311057803/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2087*100000000000000000000^512 ≤ 2387416157311057803^512*5^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2387416157311057803 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2387416157311057803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2087 := by
      have hnat : (1 : ℕ)^512*1^2087 ≤ 1^2087*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102387416157311057803/100000000000000000000 : ℝ) ≤ (2514512418001637/2500000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (102387416157311057803/100000000000000000000 : ℝ)^512 ≤ (2514512418001637/2500000000000000 : ℝ)^2087 := by
      have hnat : (102387416157311057803 : ℕ)^512*2500000000000000^2087 ≤ 2514512418001637^2087*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102387416157311057803 100000000000000000000 2514512418001637 2500000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514512418001637/2500000000000000 : ℝ)) (X := (102387416157311057803/100000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52387416157311057803/50000000000000000000 : ℝ) ≤ (1264512418001637/1250000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (52387416157311057803/50000000000000000000 : ℝ)^512 ≤ (1264512418001637/1250000000000000 : ℝ)^2087 := by
      have hnat : (52387416157311057803 : ℕ)^512*1250000000000000^2087 ≤ 1264512418001637^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52387416157311057803 50000000000000000000 1264512418001637 1250000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264512418001637/1250000000000000 : ℝ)) (X := (52387416157311057803/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14512418001637/1000000000000000 : ℝ)*(0 : ℝ))^(2087/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(14512418001637/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2387416157311057803/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14512418001637/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (1 : ℝ)+(14512418001637/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514512418001637/2500000000000000 : ℝ) by norm_num, show 1+(2387416157311057803/100000000000000000000 : ℝ)+(0 : ℝ)=(102387416157311057803/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2387416157311057803/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14512418001637/1000000000000000 : ℝ)*(2/5 : ℝ))^(2087/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(14512418001637/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264512418001637/1250000000000000 : ℝ) by norm_num, show 1+2*(2387416157311057803/100000000000000000000 : ℝ)=(52387416157311057803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14512418001637/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14512418001637/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14512418001637/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14512418001637/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14512418001637/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14512418001637/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1887387681/10000000000 : ℝ)*X 0 0+(6051100103/10000000000 : ℝ)*X 0 1+(2391120157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516005011/10000000000 : ℝ)*X 1 0+(-2615166947/10000000000 : ℝ)*X 1 1+(4782240383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((34475031/62500000 : ℝ)*X 2 0+(1195560117/2500000000 : ℝ)*X 2 1+(-261516691/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099930487/5000000000 : ℝ)*X 0 0+(1560219381/5000000000 : ℝ)*X 0 1+(5651736087/10000000000 : ℝ)*X 0 2+(2099930487/5000000000 : ℝ)*X 1 0+(1560219381/5000000000 : ℝ)*X 1 1+(5651736087/10000000000 : ℝ)*X 1 2+(2099930487/5000000000 : ℝ)*X 2 0+(1560219381/5000000000 : ℝ)*X 2 1+(5651736087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1892492191/10000000000 : ℝ)*X 0 0+(2407483149/5000000000 : ℝ)*X 0 1+(3008611243/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171159339/10000000000 : ℝ)*X 1 0+(-1380185059/10000000000 : ℝ)*X 1 1+(6017222301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((129278983/250000000 : ℝ)*X 2 0+(1504305591/2500000000 : ℝ)*X 2 1+(-345046247/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052511073/2500000000 : ℝ)*X 0 0+(2793224839/5000000000 : ℝ)*X 0 1+(3188022669/10000000000 : ℝ)*X 0 2+(1052511073/2500000000 : ℝ)*X 1 0+(2793224839/5000000000 : ℝ)*X 1 1+(3188022669/10000000000 : ℝ)*X 1 2+(1052511073/2500000000 : ℝ)*X 2 0+(2793224839/5000000000 : ℝ)*X 2 1+(3188022669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11008069957488314412069/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12666609/25000000000000 : ℝ)*(base1) + (1777391/160000000000 : ℝ)*(base19) + (128253521/12500000000000 : ℝ)*(base23) + (77554443/100000000000000 : ℝ)*(base24) + (252002601/100000000000000 : ℝ)*(upper3) + (59158649785607/10000000000000 : ℝ)*(major0) + (59158649785607/10000000000000 : ℝ)*(major1) + (59158649785607/10000000000000 : ℝ)*(major2) + (788112909390573/100000000000000 : ℝ)*(sp0) + (197028562135517/25000000000000 : ℝ)*(sp1) + (24628570494651/3125000000000 : ℝ)*(sp2) + (79011098590263/20000000000000 : ℝ)*(sp3) + (1250343653/50000000000000 : ℝ)*(sp4) + (77836347/4000000000000 : ℝ)*(sp7) + (395057489526427/100000000000000 : ℝ)*(f.failure) + (788115359411443/100000000000000 : ℝ)*(f.sum) + (9617648783659/5000000000000000000000000000 : ℝ)*base65 + (40377716168659/10000000000000000000000000000 : ℝ)*base67 + (38742618858659/10000000000000000000000000000 : ℝ)*base69 + (17679258458659/10000000000000000000000000000 : ℝ)*base71 + (17860413618659/5000000000000000000000000000 : ℝ)*base73 + (29004524798659/10000000000000000000000000000 : ℝ)*base75 + (20772218738659/10000000000000000000000000000 : ℝ)*base77 + (49401404478659/10000000000000000000000000000 : ℝ)*base79 + (18112380738659/5000000000000000000000000000 : ℝ)*base81 + (2856953/10000000000000000000000 : ℝ)*base89 + (2856953/10000000000000000000000 : ℝ)*base91 + (2856953/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15138818966514906129423/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28950303/100000000000000 : ℝ)*(base1) + (47205227/12500000000000 : ℝ)*(base19) + (23391717/6250000000000 : ℝ)*(base23) + (32178393/100000000000000 : ℝ)*(upper3) + (49702967/100000000000000 : ℝ)*(upper5) + (124870952188069/20000000000000 : ℝ)*(major0) + (124870952188069/20000000000000 : ℝ)*(major1) + (124870952188069/20000000000000 : ℝ)*(major2) + (34583571/5000000000000 : ℝ)*(sp1) + (686899339/100000000000000 : ℝ)*(sp2) + (415884792430821/50000000000000 : ℝ)*(sp4) + (831768486598103/100000000000000 : ℝ)*(sp5) + (831768494744527/100000000000000 : ℝ)*(sp6) + (208469943278157/50000000000000 : ℝ)*(sp7) + (416939915506617/100000000000000 : ℝ)*(f.failure) + (831769555911339/100000000000000 : ℝ)*(f.sum) + (5771353208953/10000000000000000000000000000 : ℝ)*base65 + (43747409708953/20000000000000000000000000000 : ℝ)*base67 + (50677707691047/20000000000000000000000000000 : ℝ)*base70 + (32771989368953/20000000000000000000000000000 : ℝ)*base71 + (9616883118953/10000000000000000000000000000 : ℝ)*base73 + (68410955288953/20000000000000000000000000000 : ℝ)*base75 + (84649118508953/20000000000000000000000000000 : ℝ)*base77 + (173421186428953/20000000000000000000000000000 : ℝ)*base79 + (38938915131047/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (29995363/10000000000000000000000 : ℝ)*base89 + (29995363/10000000000000000000000 : ℝ)*base91 + (29995363/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1156_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1156_s1_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045522231/5000000000 : ℝ)*x 0 + (2848885141/5000000000 : ℝ)*x 1 + (1001038861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045522231/5000000000 : ℝ)^8349 ≤ (6286840724727/50000000000000 : ℝ)^6301 := by
    have hnat : (1045522231 : ℕ)^8349*50000000000000^6301 ≤ 6286840724727^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045522231 5000000000 6286840724727 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848885141/5000000000 : ℝ)^8349 ≤ (2372860786299/5000000000000 : ℝ)^6301 := by
    have hnat : (2848885141 : ℕ)^8349*5000000000000^6301 ≤ 2372860786299^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848885141 5000000000 2372860786299 5000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001038861/2000000000 : ℝ)^8349 ≤ (19984551404867/50000000000000 : ℝ)^6301 := by
    have hnat : (1001038861 : ℕ)^8349*50000000000000^6301 ≤ 19984551404867^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001038861 2000000000 19984551404867 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045522231/5000000000 : ℝ), (2848885141/5000000000 : ℝ), (1001038861/2000000000 : ℝ)] ![(6286840724727/50000000000000 : ℝ), (2372860786299/5000000000000 : ℝ), (19984551404867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045522231/5000000000 : ℝ)|^8349 ≤ (6286840724727/50000000000000 : ℝ)^6301
        have hw : |(-1045522231/5000000000 : ℝ)|=(1045522231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2848885141/5000000000 : ℝ)|^8349 ≤ (2372860786299/5000000000000 : ℝ)^6301
        have hw : |(2848885141/5000000000 : ℝ)|=(2848885141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001038861/2000000000 : ℝ)|^8349 ≤ (19984551404867/50000000000000 : ℝ)^6301
        have hw : |(1001038861/2000000000 : ℝ)|=(1001038861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s1_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5418350739/10000000000 : ℝ)*x 0 + (-246453023/1000000000 : ℝ)*x 1 + (1251298349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418350739/10000000000 : ℝ)^8349 ≤ (4439831978519/10000000000000 : ℝ)^6301 := by
    have hnat : (5418350739 : ℕ)^8349*10000000000000^6301 ≤ 4439831978519^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418350739 10000000000 4439831978519 10000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246453023/1000000000 : ℝ)^8349 ≤ (3908146752521/25000000000000 : ℝ)^6301 := by
    have hnat : (246453023 : ℕ)^8349*25000000000000^6301 ≤ 3908146752521^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246453023 1000000000 3908146752521 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251298349/2500000000 : ℝ)^8349 ≤ (2498068324473/6250000000000 : ℝ)^6301 := by
    have hnat : (1251298349 : ℕ)^8349*6250000000000^6301 ≤ 2498068324473^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251298349 2500000000 2498068324473 6250000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418350739/10000000000 : ℝ), (-246453023/1000000000 : ℝ), (1251298349/2500000000 : ℝ)] ![(4439831978519/10000000000000 : ℝ), (3908146752521/25000000000000 : ℝ), (2498068324473/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418350739/10000000000 : ℝ)|^8349 ≤ (4439831978519/10000000000000 : ℝ)^6301
        have hw : |(5418350739/10000000000 : ℝ)|=(5418350739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246453023/1000000000 : ℝ)|^8349 ≤ (3908146752521/25000000000000 : ℝ)^6301
        have hw : |(-246453023/1000000000 : ℝ)|=(246453023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251298349/2500000000 : ℝ)|^8349 ≤ (2498068324473/6250000000000 : ℝ)^6301
        have hw : |(1251298349/2500000000 : ℝ)|=(1251298349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s1_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2709176413/5000000000 : ℝ)*x 0 + (31282447/62500000 : ℝ)*x 1 + (-308066237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709176413/5000000000 : ℝ)^8349 ≤ (44398342444511/100000000000000 : ℝ)^6301 := by
    have hnat : (2709176413 : ℕ)^8349*100000000000000^6301 ≤ 44398342444511^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709176413 5000000000 44398342444511 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31282447/62500000 : ℝ)^8349 ≤ (7993814668307/20000000000000 : ℝ)^6301 := by
    have hnat : (31282447 : ℕ)^8349*20000000000000^6301 ≤ 7993814668307^6301*62500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31282447 62500000 7993814668307 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (308066237/1250000000 : ℝ)^8349 ≤ (7816292101459/50000000000000 : ℝ)^6301 := by
    have hnat : (308066237 : ℕ)^8349*50000000000000^6301 ≤ 7816292101459^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308066237 1250000000 7816292101459 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709176413/5000000000 : ℝ), (31282447/62500000 : ℝ), (-308066237/1250000000 : ℝ)] ![(44398342444511/100000000000000 : ℝ), (7993814668307/20000000000000 : ℝ), (7816292101459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709176413/5000000000 : ℝ)|^8349 ≤ (44398342444511/100000000000000 : ℝ)^6301
        have hw : |(2709176413/5000000000 : ℝ)|=(2709176413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31282447/62500000 : ℝ)|^8349 ≤ (7993814668307/20000000000000 : ℝ)^6301
        have hw : |(31282447/62500000 : ℝ)|=(31282447/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-308066237/1250000000 : ℝ)|^8349 ≤ (7816292101459/50000000000000 : ℝ)^6301
        have hw : |(-308066237/1250000000 : ℝ)|=(308066237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s1_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (431625421/1000000000 : ℝ)*x 0 + (1839841373/5000000000 : ℝ)*x 1 + (632665691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431625421/1000000000 : ℝ)^8349 ≤ (1642391409701/5000000000000 : ℝ)^6301 := by
    have hnat : (431625421 : ℕ)^8349*5000000000000^6301 ≤ 1642391409701^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431625421 1000000000 1642391409701 5000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1839841373/5000000000 : ℝ)^8349 ≤ (13294031213837/50000000000000 : ℝ)^6301 := by
    have hnat : (1839841373 : ℕ)^8349*50000000000000^6301 ≤ 13294031213837^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839841373 5000000000 13294031213837 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632665691/1250000000 : ℝ)^8349 ≤ (1622564374751/4000000000000 : ℝ)^6301 := by
    have hnat : (632665691 : ℕ)^8349*4000000000000^6301 ≤ 1622564374751^6301*1250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632665691 1250000000 1622564374751 4000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431625421/1000000000 : ℝ), (1839841373/5000000000 : ℝ), (632665691/1250000000 : ℝ)] ![(1642391409701/5000000000000 : ℝ), (13294031213837/50000000000000 : ℝ), (1622564374751/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431625421/1000000000 : ℝ)|^8349 ≤ (1642391409701/5000000000000 : ℝ)^6301
        have hw : |(431625421/1000000000 : ℝ)|=(431625421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1839841373/5000000000 : ℝ)|^8349 ≤ (13294031213837/50000000000000 : ℝ)^6301
        have hw : |(1839841373/5000000000 : ℝ)|=(1839841373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(632665691/1250000000 : ℝ)|^8349 ≤ (1622564374751/4000000000000 : ℝ)^6301
        have hw : |(632665691/1250000000 : ℝ)|=(632665691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s1_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045917863/5000000000 : ℝ)*x 0 + (5014600157/10000000000 : ℝ)*x 1 + (1137635149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045917863/5000000000 : ℝ)^8349 ≤ (12579986263457/100000000000000 : ℝ)^6301 := by
    have hnat : (1045917863 : ℕ)^8349*100000000000000^6301 ≤ 12579986263457^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045917863 5000000000 12579986263457 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014600157/10000000000 : ℝ)^8349 ≤ (40068656906663/100000000000000 : ℝ)^6301 := by
    have hnat : (5014600157 : ℕ)^8349*100000000000000^6301 ≤ 40068656906663^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014600157 10000000000 40068656906663 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137635149/2000000000 : ℝ)^8349 ≤ (1894054272689/4000000000000 : ℝ)^6301 := by
    have hnat : (1137635149 : ℕ)^8349*4000000000000^6301 ≤ 1894054272689^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137635149 2000000000 1894054272689 4000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045917863/5000000000 : ℝ), (5014600157/10000000000 : ℝ), (1137635149/2000000000 : ℝ)] ![(12579986263457/100000000000000 : ℝ), (40068656906663/100000000000000 : ℝ), (1894054272689/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045917863/5000000000 : ℝ)|^8349 ≤ (12579986263457/100000000000000 : ℝ)^6301
        have hw : |(-1045917863/5000000000 : ℝ)|=(1045917863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5014600157/10000000000 : ℝ)|^8349 ≤ (40068656906663/100000000000000 : ℝ)^6301
        have hw : |(5014600157/10000000000 : ℝ)|=(5014600157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1137635149/2000000000 : ℝ)|^8349 ≤ (1894054272689/4000000000000 : ℝ)^6301
        have hw : |(1137635149/2000000000 : ℝ)|=(1137635149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s1_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1310165681/2500000000 : ℝ)*x 0 + (-1781544013/10000000000 : ℝ)*x 1 + (2844089633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310165681/2500000000 : ℝ)^8349 ≤ (265496593189/625000000000 : ℝ)^6301 := by
    have hnat : (1310165681 : ℕ)^8349*625000000000^6301 ≤ 265496593189^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310165681 2500000000 265496593189 625000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1781544013/10000000000 : ℝ)^8349 ≤ (10169149424619/100000000000000 : ℝ)^6301 := by
    have hnat : (1781544013 : ℕ)^8349*100000000000000^6301 ≤ 10169149424619^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781544013 10000000000 10169149424619 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2844089633/5000000000 : ℝ)^8349 ≤ (23675697827327/50000000000000 : ℝ)^6301 := by
    have hnat : (2844089633 : ℕ)^8349*50000000000000^6301 ≤ 23675697827327^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844089633 5000000000 23675697827327 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310165681/2500000000 : ℝ), (-1781544013/10000000000 : ℝ), (2844089633/5000000000 : ℝ)] ![(265496593189/625000000000 : ℝ), (10169149424619/100000000000000 : ℝ), (23675697827327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310165681/2500000000 : ℝ)|^8349 ≤ (265496593189/625000000000 : ℝ)^6301
        have hw : |(1310165681/2500000000 : ℝ)|=(1310165681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1781544013/10000000000 : ℝ)|^8349 ≤ (10169149424619/100000000000000 : ℝ)^6301
        have hw : |(-1781544013/10000000000 : ℝ)|=(1781544013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2844089633/5000000000 : ℝ)|^8349 ≤ (23675697827327/50000000000000 : ℝ)^6301
        have hw : |(2844089633/5000000000 : ℝ)|=(2844089633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s1_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620330801/5000000000 : ℝ)*x 0 + (5688180879/10000000000 : ℝ)*x 1 + (-1781543253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620330801/5000000000 : ℝ)^8349 ≤ (42479442859587/100000000000000 : ℝ)^6301 := by
    have hnat : (2620330801 : ℕ)^8349*100000000000000^6301 ≤ 42479442859587^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620330801 5000000000 42479442859587 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5688180879/10000000000 : ℝ)^8349 ≤ (47351413446413/100000000000000 : ℝ)^6301 := by
    have hnat : (5688180879 : ℕ)^8349*100000000000000^6301 ≤ 47351413446413^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688180879 10000000000 47351413446413 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1781543253/10000000000 : ℝ)^8349 ≤ (1271142959561/12500000000000 : ℝ)^6301 := by
    have hnat : (1781543253 : ℕ)^8349*12500000000000^6301 ≤ 1271142959561^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781543253 10000000000 1271142959561 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620330801/5000000000 : ℝ), (5688180879/10000000000 : ℝ), (-1781543253/10000000000 : ℝ)] ![(42479442859587/100000000000000 : ℝ), (47351413446413/100000000000000 : ℝ), (1271142959561/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620330801/5000000000 : ℝ)|^8349 ≤ (42479442859587/100000000000000 : ℝ)^6301
        have hw : |(2620330801/5000000000 : ℝ)|=(2620330801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5688180879/10000000000 : ℝ)|^8349 ≤ (47351413446413/100000000000000 : ℝ)^6301
        have hw : |(5688180879/10000000000 : ℝ)|=(5688180879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1781543253/10000000000 : ℝ)|^8349 ≤ (1271142959561/12500000000000 : ℝ)^6301
        have hw : |(-1781543253/10000000000 : ℝ)|=(1781543253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s1_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1079455323/2500000000 : ℝ)*x 0 + (2521281443/5000000000 : ℝ)*x 1 + (369881457/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079455323/2500000000 : ℝ)^8349 ≤ (16431815641239/50000000000000 : ℝ)^6301 := by
    have hnat : (1079455323 : ℕ)^8349*50000000000000^6301 ≤ 16431815641239^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079455323 2500000000 16431815641239 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2521281443/5000000000 : ℝ)^8349 ≤ (10091245069569/25000000000000 : ℝ)^6301 := by
    have hnat : (2521281443 : ℕ)^8349*25000000000000^6301 ≤ 10091245069569^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2521281443 5000000000 10091245069569 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369881457/1000000000 : ℝ)^8349 ≤ (1338569421131/5000000000000 : ℝ)^6301 := by
    have hnat : (369881457 : ℕ)^8349*5000000000000^6301 ≤ 1338569421131^6301*1000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369881457 1000000000 1338569421131 5000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079455323/2500000000 : ℝ), (2521281443/5000000000 : ℝ), (369881457/1000000000 : ℝ)] ![(16431815641239/50000000000000 : ℝ), (10091245069569/25000000000000 : ℝ), (1338569421131/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079455323/2500000000 : ℝ)|^8349 ≤ (16431815641239/50000000000000 : ℝ)^6301
        have hw : |(1079455323/2500000000 : ℝ)|=(1079455323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2521281443/5000000000 : ℝ)|^8349 ≤ (10091245069569/25000000000000 : ℝ)^6301
        have hw : |(2521281443/5000000000 : ℝ)|=(2521281443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(369881457/1000000000 : ℝ)|^8349 ≤ (1338569421131/5000000000000 : ℝ)^6301
        have hw : |(369881457/1000000000 : ℝ)|=(369881457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (179/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10187/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (471/100000 : ℝ) ^ (2087/512 : ℝ) ≤ (32721504807/100000000000000000000 : ℝ) := by
    have hpowers : (471/100000 : ℝ)^2087 ≤ (32721504807/100000000000000000000 : ℝ)^512 := by
      have hnat : (471 : ℕ)^2087*100000000000000000000^512 ≤ 32721504807^512*100000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        471 100000 32721504807 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (471/100000 : ℝ)) (X := (32721504807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27761/100000 : ℝ) ^ (2087/512 : ℝ) ≤ (269349291351126021/50000000000000000000 : ℝ) := by
    have hpowers : (27761/100000 : ℝ)^2087 ≤ (269349291351126021/50000000000000000000 : ℝ)^512 := by
      have hnat : (27761 : ℕ)^2087*50000000000000000000^512 ≤ 269349291351126021^512*100000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27761 100000 269349291351126021 50000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27761/100000 : ℝ)) (X := (269349291351126021/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000032721504807/50000000000000000000 : ℝ) ≤ (5000000000802751/5000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50000000032721504807/50000000000000000000 : ℝ)^512 ≤ (5000000000802751/5000000000000000 : ℝ)^2087 := by
      have hnat : (50000000032721504807 : ℕ)^512*5000000000000000^2087 ≤ 5000000000802751^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000032721504807 50000000000000000000 5000000000802751 5000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000802751/5000000000000000 : ℝ)) (X := (50000000032721504807/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100538698615423756849/100000000000000000000 : ℝ) ≤ (10013189017905197/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (100538698615423756849/100000000000000000000 : ℝ)^512 ≤ (10013189017905197/10000000000000000 : ℝ)^2087 := by
      have hnat : (100538698615423756849 : ℕ)^512*10000000000000000^2087 ≤ 10013189017905197^2087*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100538698615423756849 100000000000000000000 10013189017905197 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013189017905197/10000000000000000 : ℝ)) (X := (100538698615423756849/100000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25269349291351126021/25000000000000000000 : ℝ) ≤ (2506594508551223/2500000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (25269349291351126021/25000000000000000000 : ℝ)^512 ≤ (2506594508551223/2500000000000000 : ℝ)^2087 := by
      have hnat : (25269349291351126021 : ℕ)^512*2500000000000000^2087 ≤ 2506594508551223^2087*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25269349291351126021 25000000000000000000 2506594508551223 2500000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506594508551223/2500000000000000 : ℝ)) (X := (25269349291351126021/25000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(32721504807/100000000000000000000 : ℝ) ≤ ((27288757599045983689/27290000000000000000 : ℝ)+2*(2637803259939/545800000000000 : ℝ)*(471/100000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (27288757599045983689/27290000000000000000 : ℝ)+2*(2637803259939/545800000000000 : ℝ)*(471/100000 : ℝ)=(5000000000802751/5000000000000000 : ℝ) by norm_num, show 1+2*(32721504807/100000000000000000000 : ℝ)=(50000000032721504807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(269349291351126021/50000000000000000000 : ℝ)+(32721504807/100000000000000000000 : ℝ) ≤ ((27288757599045983689/27290000000000000000 : ℝ)+(2637803259939/545800000000000 : ℝ)*((27761/100000 : ℝ)+(471/100000 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (27288757599045983689/27290000000000000000 : ℝ)+(2637803259939/545800000000000 : ℝ)*((27761/100000 : ℝ)+(471/100000 : ℝ))=(10013189017905197/10000000000000000 : ℝ) by norm_num, show 1+(269349291351126021/50000000000000000000 : ℝ)+(32721504807/100000000000000000000 : ℝ)=(100538698615423756849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(269349291351126021/50000000000000000000 : ℝ) ≤ ((27288757599045983689/27290000000000000000 : ℝ)+2*(2637803259939/545800000000000 : ℝ)*(27761/100000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (27288757599045983689/27290000000000000000 : ℝ)+2*(2637803259939/545800000000000 : ℝ)*(27761/100000 : ℝ)=(2506594508551223/2500000000000000 : ℝ) by norm_num, show 1+2*(269349291351126021/50000000000000000000 : ℝ)=(25269349291351126021/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27288757599045983689/27290000000000000000 : ℝ)*(X 1 0+X 2 0)+(2637803259939/545800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (471/100000 : ℝ)) (hi := (27761/100000 : ℝ)) (c := (27288757599045983689/27290000000000000000 : ℝ)) (alpha := (2637803259939/545800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27288757599045983689/27290000000000000000 : ℝ)*(X 0 1+X 2 1)+(2637803259939/545800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (471/100000 : ℝ)) (hi := (27761/100000 : ℝ)) (c := (27288757599045983689/27290000000000000000 : ℝ)) (alpha := (2637803259939/545800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27288757599045983689/27290000000000000000 : ℝ)*(X 0 2+X 1 2)+(2637803259939/545800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (471/100000 : ℝ)) (hi := (27761/100000 : ℝ)) (c := (27288757599045983689/27290000000000000000 : ℝ)) (alpha := (2637803259939/545800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1045522231/5000000000 : ℝ)*X 0 0+(2848885141/5000000000 : ℝ)*X 0 1+(1001038861/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5418350739/10000000000 : ℝ)*X 1 0+(-246453023/1000000000 : ℝ)*X 1 1+(1251298349/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2709176413/5000000000 : ℝ)*X 2 0+(31282447/62500000 : ℝ)*X 2 1+(-308066237/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431625421/1000000000 : ℝ)*X 0 0+(1839841373/5000000000 : ℝ)*X 0 1+(632665691/1250000000 : ℝ)*X 0 2+(431625421/1000000000 : ℝ)*X 1 0+(1839841373/5000000000 : ℝ)*X 1 1+(632665691/1250000000 : ℝ)*X 1 2+(431625421/1000000000 : ℝ)*X 2 0+(1839841373/5000000000 : ℝ)*X 2 1+(632665691/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1045917863/5000000000 : ℝ)*X 0 0+(5014600157/10000000000 : ℝ)*X 0 1+(1137635149/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1310165681/2500000000 : ℝ)*X 1 0+(-1781544013/10000000000 : ℝ)*X 1 1+(2844089633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620330801/5000000000 : ℝ)*X 2 0+(5688180879/10000000000 : ℝ)*X 2 1+(-1781543253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079455323/2500000000 : ℝ)*X 0 0+(2521281443/5000000000 : ℝ)*X 0 1+(369881457/1000000000 : ℝ)*X 0 2+(1079455323/2500000000 : ℝ)*X 1 0+(2521281443/5000000000 : ℝ)*X 1 1+(369881457/1000000000 : ℝ)*X 1 2+(1079455323/2500000000 : ℝ)*X 2 0+(2521281443/5000000000 : ℝ)*X 2 1+(369881457/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (173811987042432151122299643/68225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112720199/50000000000000 : ℝ)*(base1) + (654184421/100000000000000 : ℝ)*(base19) + (49424101/6250000000000 : ℝ)*(base23) + (183630821/100000000000000 : ℝ)*(base37) + (6617039/3125000000000 : ℝ)*(lower2) + (108382961436129/10000000000000 : ℝ)*(major0) + (108382961436129/10000000000000 : ℝ)*(major1) + (108382961436129/10000000000000 : ℝ)*(major2) + (360971005646633/25000000000000 : ℝ)*(sp0) + (1443884353331643/100000000000000 : ℝ)*(sp1) + (3609708350093/250000000000 : ℝ)*(sp2) + (180943431803581/25000000000000 : ℝ)*(sp3) + (1210369931/100000000000000 : ℝ)*(sp4) + (876693249/100000000000000 : ℝ)*(sp6) + (90471767035693/12500000000000 : ℝ)*(f.failure) + (45121406484877/3125000000000 : ℝ)*(f.sum) + (4554043953981/2729000000000000000000000000 : ℝ)*base65 + (878665713089650119/272900000000000000000000000000000 : ℝ)*base68 + (72167626622450119/272900000000000000000000000000000 : ℝ)*base70 + (285671293663450119/272900000000000000000000000000000 : ℝ)*base72 + (210890217989/109160000000000000000000000 : ℝ)*base73 + (1343144777925849881/272900000000000000000000000000000 : ℝ)*base75 + (1205594794304350119/272900000000000000000000000000000 : ℝ)*base78 + (1099989981861650119/272900000000000000000000000000000 : ℝ)*base80 + (99778843127/21320312500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (5493727/1250000000000000000000 : ℝ)*base89 + (5493727/1250000000000000000000 : ℝ)*base91 + (5493727/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (775552756659481899153412449/341125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59557279/2500000000000 : ℝ)*(base19) + (304985237/10000000000000 : ℝ)*(base23) + (50752109/12500000000000 : ℝ)*(upper2) + (157673627/25000000000000 : ℝ)*(upper3) + (350622429/100000000000000 : ℝ)*(upper5) + (278599549189351/25000000000000 : ℝ)*(major0) + (278599549189351/25000000000000 : ℝ)*(major1) + (278599549189351/25000000000000 : ℝ)*(major2) + (13459099133/100000000000000 : ℝ)*(sp1) + (9836002269/50000000000000 : ℝ)*(sp2) + (148460868745333/10000000000000 : ℝ)*(sp4) + (371148211515759/25000000000000 : ℝ)*(sp5) + (742292982798211/50000000000000 : ℝ)*(sp6) + (18604690756941/2500000000000 : ℝ)*(sp7) + (18604690756941/2500000000000 : ℝ)*(f.failure) + (148460868745333/10000000000000 : ℝ)*(f.sum) + (7907717204661/6822500000000000000000000000 : ℝ)*base66 + (2617083295635445839/682250000000000000000000000000000 : ℝ)*base67 + (921041315585445839/682250000000000000000000000000000 : ℝ)*base69 + (5020003012698195839/682250000000000000000000000000000 : ℝ)*base71 + (120062802553/3411250000000000000000000000 : ℝ)*base74 + (7620970740778945839/682250000000000000000000000000000 : ℝ)*base75 + (328283643185945839/682250000000000000000000000000000 : ℝ)*base77 + (8141834712047445839/682250000000000000000000000000000 : ℝ)*base79 + (887545109987/852812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2246401/250000000000000000000 : ℝ)*base90 + (2246401/250000000000000000000 : ℝ)*base92 + (2246401/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1156_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (179/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10187/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1156_s2_0 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-53588071/250000000 : ℝ)*x 0 + (2754080551/5000000000 : ℝ)*x 1 + (103228397/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53588071/250000000 : ℝ)^8349 ≤ (12993500758827/100000000000000 : ℝ)^6301 := by
    have hnat : (53588071 : ℕ)^8349*100000000000000^6301 ≤ 12993500758827^6301*250000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53588071 250000000 12993500758827 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754080551/5000000000 : ℝ)^8349 ≤ (22688020254527/50000000000000 : ℝ)^6301 := by
    have hnat : (2754080551 : ℕ)^8349*50000000000000^6301 ≤ 22688020254527^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754080551 5000000000 22688020254527 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103228397/200000000 : ℝ)^8349 ≤ (41630458720947/100000000000000 : ℝ)^6301 := by
    have hnat : (103228397 : ℕ)^8349*100000000000000^6301 ≤ 41630458720947^6301*200000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103228397 200000000 41630458720947 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53588071/250000000 : ℝ), (2754080551/5000000000 : ℝ), (103228397/200000000 : ℝ)] ![(12993500758827/100000000000000 : ℝ), (22688020254527/50000000000000 : ℝ), (41630458720947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53588071/250000000 : ℝ)|^8349 ≤ (12993500758827/100000000000000 : ℝ)^6301
        have hw : |(-53588071/250000000 : ℝ)|=(53588071/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754080551/5000000000 : ℝ)|^8349 ≤ (22688020254527/50000000000000 : ℝ)^6301
        have hw : |(2754080551/5000000000 : ℝ)|=(2754080551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103228397/200000000 : ℝ)|^8349 ≤ (41630458720947/100000000000000 : ℝ)^6301
        have hw : |(103228397/200000000 : ℝ)|=(103228397/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s2_1 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686632087/5000000000 : ℝ)*x 0 + (-464739137/2000000000 : ℝ)*x 1 + (1290355567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686632087/5000000000 : ℝ)^8349 ≤ (21954730876131/50000000000000 : ℝ)^6301 := by
    have hnat : (2686632087 : ℕ)^8349*50000000000000^6301 ≤ 21954730876131^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686632087 5000000000 21954730876131 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464739137/2000000000 : ℝ)^8349 ≤ (14460053671367/100000000000000 : ℝ)^6301 := by
    have hnat : (464739137 : ℕ)^8349*100000000000000^6301 ≤ 14460053671367^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464739137 2000000000 14460053671367 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1290355567/2500000000 : ℝ)^8349 ≤ (2081524228139/5000000000000 : ℝ)^6301 := by
    have hnat : (1290355567 : ℕ)^8349*5000000000000^6301 ≤ 2081524228139^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290355567 2500000000 2081524228139 5000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686632087/5000000000 : ℝ), (-464739137/2000000000 : ℝ), (1290355567/2500000000 : ℝ)] ![(21954730876131/50000000000000 : ℝ), (14460053671367/100000000000000 : ℝ), (2081524228139/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686632087/5000000000 : ℝ)|^8349 ≤ (21954730876131/50000000000000 : ℝ)^6301
        have hw : |(2686632087/5000000000 : ℝ)|=(2686632087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-464739137/2000000000 : ℝ)|^8349 ≤ (14460053671367/100000000000000 : ℝ)^6301
        have hw : |(-464739137/2000000000 : ℝ)|=(464739137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1290355567/2500000000 : ℝ)|^8349 ≤ (2081524228139/5000000000000 : ℝ)^6301
        have hw : |(1290355567/2500000000 : ℝ)|=(1290355567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s2_2 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343316097/2500000000 : ℝ)*x 0 + (161294431/312500000 : ℝ)*x 1 + (-2323696021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343316097/2500000000 : ℝ)^8349 ≤ (10977366017359/25000000000000 : ℝ)^6301 := by
    have hnat : (1343316097 : ℕ)^8349*25000000000000^6301 ≤ 10977366017359^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343316097 2500000000 10977366017359 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161294431/312500000 : ℝ)^8349 ≤ (41630479475637/100000000000000 : ℝ)^6301 := by
    have hnat : (161294431 : ℕ)^8349*100000000000000^6301 ≤ 41630479475637^6301*312500000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161294431 312500000 41630479475637 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2323696021/10000000000 : ℝ)^8349 ≤ (14460056441847/100000000000000 : ℝ)^6301 := by
    have hnat : (2323696021 : ℕ)^8349*100000000000000^6301 ≤ 14460056441847^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323696021 10000000000 14460056441847 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343316097/2500000000 : ℝ), (161294431/312500000 : ℝ), (-2323696021/10000000000 : ℝ)] ![(10977366017359/25000000000000 : ℝ), (41630479475637/100000000000000 : ℝ), (14460056441847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343316097/2500000000 : ℝ)|^8349 ≤ (10977366017359/25000000000000 : ℝ)^6301
        have hw : |(1343316097/2500000000 : ℝ)|=(1343316097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161294431/312500000 : ℝ)|^8349 ≤ (41630479475637/100000000000000 : ℝ)^6301
        have hw : |(161294431/312500000 : ℝ)|=(161294431/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2323696021/10000000000 : ℝ)|^8349 ≤ (14460056441847/100000000000000 : ℝ)^6301
        have hw : |(-2323696021/10000000000 : ℝ)|=(2323696021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s2_3 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352292107/10000000000 : ℝ)*x 0 + (1005001413/2500000000 : ℝ)*x 1 + (4711728327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352292107/10000000000 : ℝ)^8349 ≤ (33211719645331/100000000000000 : ℝ)^6301 := by
    have hnat : (4352292107 : ℕ)^8349*100000000000000^6301 ≤ 33211719645331^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352292107 10000000000 33211719645331 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005001413/2500000000 : ℝ)^8349 ≤ (7473591329579/25000000000000 : ℝ)^6301 := by
    have hnat : (1005001413 : ℕ)^8349*25000000000000^6301 ≤ 7473591329579^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005001413 2500000000 7473591329579 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4711728327/10000000000 : ℝ)^8349 ≤ (36893915028149/100000000000000 : ℝ)^6301 := by
    have hnat : (4711728327 : ℕ)^8349*100000000000000^6301 ≤ 36893915028149^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4711728327 10000000000 36893915028149 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352292107/10000000000 : ℝ), (1005001413/2500000000 : ℝ), (4711728327/10000000000 : ℝ)] ![(33211719645331/100000000000000 : ℝ), (7473591329579/25000000000000 : ℝ), (36893915028149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352292107/10000000000 : ℝ)|^8349 ≤ (33211719645331/100000000000000 : ℝ)^6301
        have hw : |(4352292107/10000000000 : ℝ)|=(4352292107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005001413/2500000000 : ℝ)|^8349 ≤ (7473591329579/25000000000000 : ℝ)^6301
        have hw : |(1005001413/2500000000 : ℝ)|=(1005001413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4711728327/10000000000 : ℝ)|^8349 ≤ (36893915028149/100000000000000 : ℝ)^6301
        have hw : |(4711728327/10000000000 : ℝ)|=(4711728327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s2_4 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-428724217/2000000000 : ℝ)*x 0 + (1032757607/2000000000 : ℝ)*x 1 + (1101153961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428724217/2000000000 : ℝ)^8349 ≤ (12994289867349/100000000000000 : ℝ)^6301 := by
    have hnat : (428724217 : ℕ)^8349*100000000000000^6301 ≤ 12994289867349^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428724217 2000000000 12994289867349 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032757607/2000000000 : ℝ)^8349 ≤ (333246160421/800000000000 : ℝ)^6301 := by
    have hnat : (1032757607 : ℕ)^8349*800000000000^6301 ≤ 333246160421^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032757607 2000000000 333246160421 800000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101153961/2000000000 : ℝ)^8349 ≤ (1813997602787/4000000000000 : ℝ)^6301 := by
    have hnat : (1101153961 : ℕ)^8349*4000000000000^6301 ≤ 1813997602787^6301*2000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101153961 2000000000 1813997602787 4000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428724217/2000000000 : ℝ), (1032757607/2000000000 : ℝ), (1101153961/2000000000 : ℝ)] ![(12994289867349/100000000000000 : ℝ), (333246160421/800000000000 : ℝ), (1813997602787/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428724217/2000000000 : ℝ)|^8349 ≤ (12994289867349/100000000000000 : ℝ)^6301
        have hw : |(-428724217/2000000000 : ℝ)|=(428724217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032757607/2000000000 : ℝ)|^8349 ≤ (333246160421/800000000000 : ℝ)^6301
        have hw : |(1032757607/2000000000 : ℝ)|=(1032757607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101153961/2000000000 : ℝ)|^8349 ≤ (1813997602787/4000000000000 : ℝ)^6301
        have hw : |(1101153961/2000000000 : ℝ)|=(1101153961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s2_5 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285204763/10000000000 : ℝ)*x 0 + (-1979347127/10000000000 : ℝ)*x 1 + (2752884897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285204763/10000000000 : ℝ)^8349 ≤ (10739627681483/25000000000000 : ℝ)^6301 := by
    have hnat : (5285204763 : ℕ)^8349*25000000000000^6301 ≤ 10739627681483^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285204763 10000000000 10739627681483 25000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1979347127/10000000000 : ℝ)^8349 ≤ (11691549312157/100000000000000 : ℝ)^6301 := by
    have hnat : (1979347127 : ℕ)^8349*100000000000000^6301 ≤ 11691549312157^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979347127 10000000000 11691549312157 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2752884897/5000000000 : ℝ)^8349 ≤ (22674969974811/50000000000000 : ℝ)^6301 := by
    have hnat : (2752884897 : ℕ)^8349*50000000000000^6301 ≤ 22674969974811^6301*5000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752884897 5000000000 22674969974811 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285204763/10000000000 : ℝ), (-1979347127/10000000000 : ℝ), (2752884897/5000000000 : ℝ)] ![(10739627681483/25000000000000 : ℝ), (11691549312157/100000000000000 : ℝ), (22674969974811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285204763/10000000000 : ℝ)|^8349 ≤ (10739627681483/25000000000000 : ℝ)^6301
        have hw : |(5285204763/10000000000 : ℝ)|=(5285204763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1979347127/10000000000 : ℝ)|^8349 ≤ (11691549312157/100000000000000 : ℝ)^6301
        have hw : |(-1979347127/10000000000 : ℝ)|=(1979347127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2752884897/5000000000 : ℝ)|^8349 ≤ (22674969974811/50000000000000 : ℝ)^6301
        have hw : |(2752884897/5000000000 : ℝ)|=(2752884897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s2_6 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285204871/10000000000 : ℝ)*x 0 + (5505769787/10000000000 : ℝ)*x 1 + (-494836747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285204871/10000000000 : ℝ)^8349 ≤ (42958511889083/100000000000000 : ℝ)^6301 := by
    have hnat : (5285204871 : ℕ)^8349*100000000000000^6301 ≤ 42958511889083^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285204871 10000000000 42958511889083 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505769787/10000000000 : ℝ)^8349 ≤ (5668742484153/12500000000000 : ℝ)^6301 := by
    have hnat : (5505769787 : ℕ)^8349*12500000000000^6301 ≤ 5668742484153^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505769787 10000000000 5668742484153 12500000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494836747/2500000000 : ℝ)^8349 ≤ (2338309644851/20000000000000 : ℝ)^6301 := by
    have hnat : (494836747 : ℕ)^8349*20000000000000^6301 ≤ 2338309644851^6301*2500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494836747 2500000000 2338309644851 20000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285204871/10000000000 : ℝ), (5505769787/10000000000 : ℝ), (-494836747/2500000000 : ℝ)] ![(42958511889083/100000000000000 : ℝ), (5668742484153/12500000000000 : ℝ), (2338309644851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285204871/10000000000 : ℝ)|^8349 ≤ (42958511889083/100000000000000 : ℝ)^6301
        have hw : |(5285204871/10000000000 : ℝ)|=(5285204871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505769787/10000000000 : ℝ)|^8349 ≤ (5668742484153/12500000000000 : ℝ)^6301
        have hw : |(5505769787/10000000000 : ℝ)|=(5505769787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494836747/2500000000 : ℝ)|^8349 ≤ (2338309644851/20000000000000 : ℝ)^6301
        have hw : |(-494836747/2500000000 : ℝ)|=(494836747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1156_s2_7 (p : ℝ) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352489673/10000000000 : ℝ)*x 0 + (4707006257/10000000000 : ℝ)*x 1 + (201238667/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352489673/10000000000 : ℝ)^8349 ≤ (16606858634603/50000000000000 : ℝ)^6301 := by
    have hnat : (4352489673 : ℕ)^8349*50000000000000^6301 ≤ 16606858634603^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352489673 10000000000 16606858634603 50000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4707006257/10000000000 : ℝ)^8349 ≤ (36844930249679/100000000000000 : ℝ)^6301 := by
    have hnat : (4707006257 : ℕ)^8349*100000000000000^6301 ≤ 36844930249679^6301*10000000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4707006257 10000000000 36844930249679 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201238667/500000000 : ℝ)^8349 ≤ (29941352474173/100000000000000 : ℝ)^6301 := by
    have hnat : (201238667 : ℕ)^8349*100000000000000^6301 ≤ 29941352474173^6301*500000000^8349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201238667 500000000 29941352474173 100000000000000 8349 6301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8349/2048 : ℝ)) 8349 6301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352489673/10000000000 : ℝ), (4707006257/10000000000 : ℝ), (201238667/500000000 : ℝ)] ![(16606858634603/50000000000000 : ℝ), (36844930249679/100000000000000 : ℝ), (29941352474173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352489673/10000000000 : ℝ)|^8349 ≤ (16606858634603/50000000000000 : ℝ)^6301
        have hw : |(4352489673/10000000000 : ℝ)|=(4352489673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4707006257/10000000000 : ℝ)|^8349 ≤ (36844930249679/100000000000000 : ℝ)^6301
        have hw : |(4707006257/10000000000 : ℝ)|=(4707006257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201238667/500000000 : ℝ)|^8349 ≤ (29941352474173/100000000000000 : ℝ)^6301
        have hw : |(201238667/500000000 : ℝ)|=(201238667/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1156_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10187/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (179/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (9133/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16461/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10187/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (179/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10187/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (179/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10187/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (179/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10187/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (179/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10187/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (179/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10187/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (179/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (179/3125 : ℝ) ^ (2087/512 : ℝ) ≤ (865778501910759/100000000000000000000 : ℝ) := by
    have hpowers : (179/3125 : ℝ)^2087 ≤ (865778501910759/100000000000000000000 : ℝ)^512 := by
      have hnat : (179 : ℕ)^2087*100000000000000000000^512 ≤ 865778501910759^512*3125^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        179 3125 865778501910759 100000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (179/3125 : ℝ)) (X := (865778501910759/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hpowhi : (10187/50000 : ℝ) ^ (2087/512 : ℝ) ≤ (3052855506619011/2000000000000000000 : ℝ) := by
    have hpowers : (10187/50000 : ℝ)^2087 ≤ (3052855506619011/2000000000000000000 : ℝ)^512 := by
      have hnat : (10187 : ℕ)^2087*2000000000000000000^512 ≤ 3052855506619011^512*50000^2087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10187 50000 3052855506619011 2000000000000000000 2087 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10187/50000 : ℝ)) (X := (3052855506619011/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000865778501910759/50000000000000000000 : ℝ) ≤ (10000042479702609/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (50000865778501910759/50000000000000000000 : ℝ)^512 ≤ (10000042479702609/10000000000000000 : ℝ)^2087 := by
      have hnat : (50000865778501910759 : ℕ)^512*10000000000000000^2087 ≤ 10000042479702609^2087*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000865778501910759 50000000000000000000 10000042479702609 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000042479702609/10000000000000000 : ℝ)) (X := (50000865778501910759/50000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100153508553832861309/100000000000000000000 : ℝ) ≤ (5001881909295719/5000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (100153508553832861309/100000000000000000000 : ℝ)^512 ≤ (5001881909295719/5000000000000000 : ℝ)^2087 := by
      have hnat : (100153508553832861309 : ℕ)^512*5000000000000000^2087 ≤ 5001881909295719^2087*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100153508553832861309 100000000000000000000 5001881909295719 5000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001881909295719/5000000000000000 : ℝ)) (X := (100153508553832861309/100000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1003052855506619011/1000000000000000000 : ℝ) ≤ (10007485157480267/10000000000000000 : ℝ) ^ (2087/512 : ℝ) := by
    have hpowers : (1003052855506619011/1000000000000000000 : ℝ)^512 ≤ (10007485157480267/10000000000000000 : ℝ)^2087 := by
      have hnat : (1003052855506619011 : ℕ)^512*10000000000000000^2087 ≤ 10007485157480267^2087*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1003052855506619011 1000000000000000000 10007485157480267 10000000000000000 512 2087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007485157480267/10000000000000000 : ℝ)) (X := (1003052855506619011/1000000000000000000 : ℝ)) (by norm_num) 2087 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(865778501910759/100000000000000000000 : ℝ) ≤ ((14641799049941398639/14646000000000000000 : ℝ)+2*(3721338888829/1464600000000000 : ℝ)*(179/3125 : ℝ))^(2087/512 : ℝ) := by
    rw [show (14641799049941398639/14646000000000000000 : ℝ)+2*(3721338888829/1464600000000000 : ℝ)*(179/3125 : ℝ)=(10000042479702609/10000000000000000 : ℝ) by norm_num, show 1+2*(865778501910759/100000000000000000000 : ℝ)=(50000865778501910759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3052855506619011/2000000000000000000 : ℝ)+(865778501910759/100000000000000000000 : ℝ) ≤ ((14641799049941398639/14646000000000000000 : ℝ)+(3721338888829/1464600000000000 : ℝ)*((10187/50000 : ℝ)+(179/3125 : ℝ)))^(2087/512 : ℝ) := by
    rw [show (14641799049941398639/14646000000000000000 : ℝ)+(3721338888829/1464600000000000 : ℝ)*((10187/50000 : ℝ)+(179/3125 : ℝ))=(5001881909295719/5000000000000000 : ℝ) by norm_num, show 1+(3052855506619011/2000000000000000000 : ℝ)+(865778501910759/100000000000000000000 : ℝ)=(100153508553832861309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3052855506619011/2000000000000000000 : ℝ) ≤ ((14641799049941398639/14646000000000000000 : ℝ)+2*(3721338888829/1464600000000000 : ℝ)*(10187/50000 : ℝ))^(2087/512 : ℝ) := by
    rw [show (14641799049941398639/14646000000000000000 : ℝ)+2*(3721338888829/1464600000000000 : ℝ)*(10187/50000 : ℝ)=(10007485157480267/10000000000000000 : ℝ) by norm_num, show 1+2*(3052855506619011/2000000000000000000 : ℝ)=(1003052855506619011/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14641799049941398639/14646000000000000000 : ℝ)*(X 1 0+X 2 0)+(3721338888829/1464600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (179/3125 : ℝ)) (hi := (10187/50000 : ℝ)) (c := (14641799049941398639/14646000000000000000 : ℝ)) (alpha := (3721338888829/1464600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14641799049941398639/14646000000000000000 : ℝ)*(X 0 1+X 2 1)+(3721338888829/1464600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (179/3125 : ℝ)) (hi := (10187/50000 : ℝ)) (c := (14641799049941398639/14646000000000000000 : ℝ)) (alpha := (3721338888829/1464600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14641799049941398639/14646000000000000000 : ℝ)*(X 0 2+X 1 2)+(3721338888829/1464600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2087/512 : ℝ)) (lo := (179/3125 : ℝ)) (hi := (10187/50000 : ℝ)) (c := (14641799049941398639/14646000000000000000 : ℝ)) (alpha := (3721338888829/1464600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53588071/250000000 : ℝ)*X 0 0+(2754080551/5000000000 : ℝ)*X 0 1+(103228397/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686632087/5000000000 : ℝ)*X 1 0+(-464739137/2000000000 : ℝ)*X 1 1+(1290355567/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343316097/2500000000 : ℝ)*X 2 0+(161294431/312500000 : ℝ)*X 2 1+(-2323696021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352292107/10000000000 : ℝ)*X 0 0+(1005001413/2500000000 : ℝ)*X 0 1+(4711728327/10000000000 : ℝ)*X 0 2+(4352292107/10000000000 : ℝ)*X 1 0+(1005001413/2500000000 : ℝ)*X 1 1+(4711728327/10000000000 : ℝ)*X 1 2+(4352292107/10000000000 : ℝ)*X 2 0+(1005001413/2500000000 : ℝ)*X 2 1+(4711728327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-428724217/2000000000 : ℝ)*X 0 0+(1032757607/2000000000 : ℝ)*X 0 1+(1101153961/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5285204763/10000000000 : ℝ)*X 1 0+(-1979347127/10000000000 : ℝ)*X 1 1+(2752884897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285204871/10000000000 : ℝ)*X 2 0+(5505769787/10000000000 : ℝ)*X 2 1+(-494836747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352489673/10000000000 : ℝ)*X 0 0+(4707006257/10000000000 : ℝ)*X 0 1+(201238667/500000000 : ℝ)*X 0 2+(4352489673/10000000000 : ℝ)*X 1 0+(4707006257/10000000000 : ℝ)*X 1 1+(201238667/500000000 : ℝ)*X 1 2+(4352489673/10000000000 : ℝ)*X 2 0+(4707006257/10000000000 : ℝ)*X 2 1+(201238667/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1156_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1120705841527081170739265841/122050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245236371/25000000000000 : ℝ)*(base19) + (821918889/100000000000000 : ℝ)*(base23) + (26514129/100000000000000 : ℝ)*(upper2) + (399492141/100000000000000 : ℝ)*(upper3) + (173681861/100000000000000 : ℝ)*(upper4) + (1082431526920319/50000000000000 : ℝ)*(major0) + (1082431526920319/50000000000000 : ℝ)*(major1) + (1082431526920319/50000000000000 : ℝ)*(major2) + (1442011181015209/50000000000000 : ℝ)*(sp0) + (721010953722587/25000000000000 : ℝ)*(sp1) + (180252748369809/6250000000000 : ℝ)*(sp2) + (1445671552143413/100000000000000 : ℝ)*(sp3) + (11216902707/50000000000000 : ℝ)*(sp4) + (4726811841/50000000000000 : ℝ)*(sp7) + (722840502883547/50000000000000 : ℝ)*(f.failure) + (360505599479479/12500000000000 : ℝ)*(f.sum) + (17957688673123/18307500000000000000000000000 : ℝ)*base65 + (274733332702244159/732300000000000000000000000000000 : ℝ)*base68 + (2211922277249744159/732300000000000000000000000000000 : ℝ)*base70 + (888546499214144159/732300000000000000000000000000000 : ℝ)*base72 + (88807187008099/36615000000000000000000000000 : ℝ)*base74 + (182883486434055841/732300000000000000000000000000000 : ℝ)*base75 + (1927092689570144159/732300000000000000000000000000000 : ℝ)*base78 + (1292519366737155841/732300000000000000000000000000000 : ℝ)*base79 + (93308746635677/18307500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (63287367/5000000000000000000000 : ℝ)*base90 + (63287367/5000000000000000000000 : ℝ)*base92 + (63287367/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (345884670822118026875136747/61025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1328688197/100000000000000 : ℝ)*(base19) + (56865383/4000000000000 : ℝ)*(base23) + (156322501/100000000000000 : ℝ)*(upper3) + (409019/25000000000000 : ℝ)*(lower4) + (3875107/3125000000000 : ℝ)*(upper5) + (1097476968135027/50000000000000 : ℝ)*(major0) + (1097476968135027/50000000000000 : ℝ)*(major1) + (1097476968135027/50000000000000 : ℝ)*(major2) + (12708208527/100000000000000 : ℝ)*(sp1) + (1451462777/10000000000000 : ℝ)*(sp2) + (2924132188679331/100000000000000 : ℝ)*(sp4) + (2924118151782607/100000000000000 : ℝ)*(sp5) + (1462058126208493/50000000000000 : ℝ)*(sp6) + (732887747465093/50000000000000 : ℝ)*(sp7) + (732887747465093/50000000000000 : ℝ)*(f.failure) + (2924132188679331/100000000000000 : ℝ)*(f.sum) + (30678646297677/6102500000000000000000000000 : ℝ)*base66 + (27515643373252751/244100000000000000000000000000000 : ℝ)*base67 + (1520366969890452751/244100000000000000000000000000000 : ℝ)*base69 + (487409897690252751/244100000000000000000000000000000 : ℝ)*base71 + (58066491093729/12205000000000000000000000000 : ℝ)*base74 + (1746635040400552751/244100000000000000000000000000000 : ℝ)*base75 + (1405268681829552751/244100000000000000000000000000000 : ℝ)*base77 + (26469814578447249/244100000000000000000000000000000 : ℝ)*base80 + (26989536499449/12205000000000000000000000000 : ℝ)*base82 + (13899673/5000000000000000000000 : ℝ)*base90 + (13899673/5000000000000000000000 : ℝ)*base92 + (13899673/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1156_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10187/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (179/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9133/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1156_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1156_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9133/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1156_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1156_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1156_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2087/512 : ℝ) ≤ p) (hpb : p ≤ (8349/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149746939/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9133/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1156_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
