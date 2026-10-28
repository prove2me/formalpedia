-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1069_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:09:05.697244+00:00
-- url     : https://prove2.me/submissions/7198aeca-1364-4c31-aedf-0342489f535a

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
theorem support_rectangle_w1069_s0_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-239391461/1250000000 : ℝ)*x 0 + (3035678239/5000000000 : ℝ)*x 1 + (190846851/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239391461/1250000000 : ℝ)^4131 ≤ (2776942251613/25000000000000 : ℝ)^3107 := by
    have hnat : (239391461 : ℕ)^4131*25000000000000^3107 ≤ 2776942251613^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239391461 1250000000 2776942251613 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3035678239/5000000000 : ℝ)^4131 ≤ (51506423919827/100000000000000 : ℝ)^3107 := by
    have hnat : (3035678239 : ℕ)^4131*100000000000000^3107 ≤ 51506423919827^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3035678239 5000000000 51506423919827 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190846851/400000000 : ℝ)^4131 ≤ (37385807057823/100000000000000 : ℝ)^3107 := by
    have hnat : (190846851 : ℕ)^4131*100000000000000^3107 ≤ 37385807057823^3107*400000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190846851 400000000 37385807057823 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239391461/1250000000 : ℝ), (3035678239/5000000000 : ℝ), (190846851/400000000 : ℝ)] ![(2776942251613/25000000000000 : ℝ), (51506423919827/100000000000000 : ℝ), (37385807057823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239391461/1250000000 : ℝ)|^4131 ≤ (2776942251613/25000000000000 : ℝ)^3107
        have hw : |(-239391461/1250000000 : ℝ)|=(239391461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3035678239/5000000000 : ℝ)|^4131 ≤ (51506423919827/100000000000000 : ℝ)^3107
        have hw : |(3035678239/5000000000 : ℝ)|=(3035678239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190846851/400000000 : ℝ)|^4131 ≤ (37385807057823/100000000000000 : ℝ)^3107
        have hw : |(190846851/400000000 : ℝ)|=(190846851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s0_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1380225613/2500000000 : ℝ)*x 0 + (-2663437131/10000000000 : ℝ)*x 1 + (954234419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380225613/2500000000 : ℝ)^4131 ≤ (45392298457657/100000000000000 : ℝ)^3107 := by
    have hnat : (1380225613 : ℕ)^4131*100000000000000^3107 ≤ 45392298457657^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380225613 2500000000 45392298457657 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2663437131/10000000000 : ℝ)^4131 ≤ (1722188592959/10000000000000 : ℝ)^3107 := by
    have hnat : (2663437131 : ℕ)^4131*10000000000000^3107 ≤ 1722188592959^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663437131 10000000000 1722188592959 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954234419/2000000000 : ℝ)^4131 ≤ (37385815600807/100000000000000 : ℝ)^3107 := by
    have hnat : (954234419 : ℕ)^4131*100000000000000^3107 ≤ 37385815600807^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954234419 2000000000 37385815600807 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380225613/2500000000 : ℝ), (-2663437131/10000000000 : ℝ), (954234419/2000000000 : ℝ)] ![(45392298457657/100000000000000 : ℝ), (1722188592959/10000000000000 : ℝ), (37385815600807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380225613/2500000000 : ℝ)|^4131 ≤ (45392298457657/100000000000000 : ℝ)^3107
        have hw : |(1380225613/2500000000 : ℝ)|=(1380225613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2663437131/10000000000 : ℝ)|^4131 ≤ (1722188592959/10000000000000 : ℝ)^3107
        have hw : |(-2663437131/10000000000 : ℝ)|=(2663437131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(954234419/2000000000 : ℝ)|^4131 ≤ (37385815600807/100000000000000 : ℝ)^3107
        have hw : |(954234419/2000000000 : ℝ)|=(954234419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s0_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2760453161/5000000000 : ℝ)*x 0 + (4771170093/10000000000 : ℝ)*x 1 + (-665858659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760453161/5000000000 : ℝ)^4131 ≤ (45392340763179/100000000000000 : ℝ)^3107 := by
    have hnat : (2760453161 : ℕ)^4131*100000000000000^3107 ≤ 45392340763179^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760453161 5000000000 45392340763179 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4771170093/10000000000 : ℝ)^4131 ≤ (18692897371713/50000000000000 : ℝ)^3107 := by
    have hnat : (4771170093 : ℕ)^4131*50000000000000^3107 ≤ 18692897371713^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771170093 10000000000 18692897371713 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (665858659/2500000000 : ℝ)^4131 ≤ (8610932239909/50000000000000 : ℝ)^3107 := by
    have hnat : (665858659 : ℕ)^4131*50000000000000^3107 ≤ 8610932239909^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665858659 2500000000 8610932239909 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760453161/5000000000 : ℝ), (4771170093/10000000000 : ℝ), (-665858659/2500000000 : ℝ)] ![(45392340763179/100000000000000 : ℝ), (18692897371713/50000000000000 : ℝ), (8610932239909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760453161/5000000000 : ℝ)|^4131 ≤ (45392340763179/100000000000000 : ℝ)^3107
        have hw : |(2760453161/5000000000 : ℝ)|=(2760453161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4771170093/10000000000 : ℝ)|^4131 ≤ (18692897371713/50000000000000 : ℝ)^3107
        have hw : |(4771170093/10000000000 : ℝ)|=(4771170093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-665858659/2500000000 : ℝ)|^4131 ≤ (8610932239909/50000000000000 : ℝ)^3107
        have hw : |(-665858659/2500000000 : ℝ)|=(665858659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s0_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206963011/10000000000 : ℝ)*x 0 + (1562352627/5000000000 : ℝ)*x 1 + (567440671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206963011/10000000000 : ℝ)^4131 ≤ (7906366034977/25000000000000 : ℝ)^3107 := by
    have hnat : (4206963011 : ℕ)^4131*25000000000000^3107 ≤ 7906366034977^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206963011 10000000000 7906366034977 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562352627/5000000000 : ℝ)^4131 ≤ (21296539964249/100000000000000 : ℝ)^3107 := by
    have hnat : (1562352627 : ℕ)^4131*100000000000000^3107 ≤ 21296539964249^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562352627 5000000000 21296539964249 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567440671/1000000000 : ℝ)^4131 ≤ (47077995872767/100000000000000 : ℝ)^3107 := by
    have hnat : (567440671 : ℕ)^4131*100000000000000^3107 ≤ 47077995872767^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567440671 1000000000 47077995872767 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206963011/10000000000 : ℝ), (1562352627/5000000000 : ℝ), (567440671/1000000000 : ℝ)] ![(7906366034977/25000000000000 : ℝ), (21296539964249/100000000000000 : ℝ), (47077995872767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206963011/10000000000 : ℝ)|^4131 ≤ (7906366034977/25000000000000 : ℝ)^3107
        have hw : |(4206963011/10000000000 : ℝ)|=(4206963011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562352627/5000000000 : ℝ)|^4131 ≤ (21296539964249/100000000000000 : ℝ)^3107
        have hw : |(1562352627/5000000000 : ℝ)|=(1562352627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567440671/1000000000 : ℝ)|^4131 ≤ (47077995872767/100000000000000 : ℝ)^3107
        have hw : |(567440671/1000000000 : ℝ)|=(567440671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s0_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920495993/10000000000 : ℝ)*x 0 + (4804741401/10000000000 : ℝ)*x 1 + (6036611667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920495993/10000000000 : ℝ)^4131 ≤ (1114915523869/10000000000000 : ℝ)^3107 := by
    have hnat : (1920495993 : ℕ)^4131*10000000000000^3107 ≤ 1114915523869^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920495993 10000000000 1114915523869 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4804741401/10000000000 : ℝ)^4131 ≤ (2358497165117/6250000000000 : ℝ)^3107 := by
    have hnat : (4804741401 : ℕ)^4131*6250000000000^3107 ≤ 2358497165117^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804741401 10000000000 2358497165117 6250000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6036611667/10000000000 : ℝ)^4131 ≤ (51114890099751/100000000000000 : ℝ)^3107 := by
    have hnat : (6036611667 : ℕ)^4131*100000000000000^3107 ≤ 51114890099751^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036611667 10000000000 51114890099751 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920495993/10000000000 : ℝ), (4804741401/10000000000 : ℝ), (6036611667/10000000000 : ℝ)] ![(1114915523869/10000000000000 : ℝ), (2358497165117/6250000000000 : ℝ), (51114890099751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920495993/10000000000 : ℝ)|^4131 ≤ (1114915523869/10000000000000 : ℝ)^3107
        have hw : |(-1920495993/10000000000 : ℝ)|=(1920495993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4804741401/10000000000 : ℝ)|^4131 ≤ (2358497165117/6250000000000 : ℝ)^3107
        have hw : |(4804741401/10000000000 : ℝ)|=(4804741401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6036611667/10000000000 : ℝ)|^4131 ≤ (51114890099751/100000000000000 : ℝ)^3107
        have hw : |(6036611667/10000000000 : ℝ)|=(6036611667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s0_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (516799677/1000000000 : ℝ)*x 0 + (-698999607/5000000000 : ℝ)*x 1 + (3018304751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516799677/1000000000 : ℝ)^4131 ≤ (20787843878009/50000000000000 : ℝ)^3107 := by
    have hnat : (516799677 : ℕ)^4131*50000000000000^3107 ≤ 20787843878009^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516799677 1000000000 20787843878009 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698999607/5000000000 : ℝ)^4131 ≤ (3654723251731/50000000000000 : ℝ)^3107 := by
    have hnat : (698999607 : ℕ)^4131*50000000000000^3107 ≤ 3654723251731^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698999607 5000000000 3654723251731 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3018304751/5000000000 : ℝ)^4131 ≤ (10222973145159/20000000000000 : ℝ)^3107 := by
    have hnat : (3018304751 : ℕ)^4131*20000000000000^3107 ≤ 10222973145159^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3018304751 5000000000 10222973145159 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516799677/1000000000 : ℝ), (-698999607/5000000000 : ℝ), (3018304751/5000000000 : ℝ)] ![(20787843878009/50000000000000 : ℝ), (3654723251731/50000000000000 : ℝ), (10222973145159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516799677/1000000000 : ℝ)|^4131 ≤ (20787843878009/50000000000000 : ℝ)^3107
        have hw : |(516799677/1000000000 : ℝ)|=(516799677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698999607/5000000000 : ℝ)|^4131 ≤ (3654723251731/50000000000000 : ℝ)^3107
        have hw : |(-698999607/5000000000 : ℝ)|=(698999607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3018304751/5000000000 : ℝ)|^4131 ≤ (10222973145159/20000000000000 : ℝ)^3107
        have hw : |(3018304751/5000000000 : ℝ)|=(3018304751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s0_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2583998401/5000000000 : ℝ)*x 0 + (3018305429/5000000000 : ℝ)*x 1 + (-1397996969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583998401/5000000000 : ℝ)^4131 ≤ (20787844049149/50000000000000 : ℝ)^3107 := by
    have hnat : (2583998401 : ℕ)^4131*50000000000000^3107 ≤ 20787844049149^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583998401 5000000000 20787844049149 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3018305429/5000000000 : ℝ)^4131 ≤ (12778720247971/25000000000000 : ℝ)^3107 := by
    have hnat : (3018305429 : ℕ)^4131*25000000000000^3107 ≤ 12778720247971^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3018305429 5000000000 12778720247971 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1397996969/10000000000 : ℝ)^4131 ≤ (3654715448441/50000000000000 : ℝ)^3107 := by
    have hnat : (1397996969 : ℕ)^4131*50000000000000^3107 ≤ 3654715448441^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397996969 10000000000 3654715448441 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583998401/5000000000 : ℝ), (3018305429/5000000000 : ℝ), (-1397996969/10000000000 : ℝ)] ![(20787844049149/50000000000000 : ℝ), (12778720247971/25000000000000 : ℝ), (3654715448441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583998401/5000000000 : ℝ)|^4131 ≤ (20787844049149/50000000000000 : ℝ)^3107
        have hw : |(2583998401/5000000000 : ℝ)|=(2583998401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3018305429/5000000000 : ℝ)|^4131 ≤ (12778720247971/25000000000000 : ℝ)^3107
        have hw : |(3018305429/5000000000 : ℝ)|=(3018305429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1397996969/10000000000 : ℝ)|^4131 ≤ (3654715448441/50000000000000 : ℝ)^3107
        have hw : |(-1397996969/10000000000 : ℝ)|=(1397996969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s0_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210873969/500000000 : ℝ)*x 0 + (5608571827/10000000000 : ℝ)*x 1 + (3192844607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210873969/500000000 : ℝ)^4131 ≤ (31730618367039/100000000000000 : ℝ)^3107 := by
    have hnat : (210873969 : ℕ)^4131*100000000000000^3107 ≤ 31730618367039^3107*500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210873969 500000000 31730618367039 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5608571827/10000000000 : ℝ)^4131 ≤ (46353169097871/100000000000000 : ℝ)^3107 := by
    have hnat : (5608571827 : ℕ)^4131*100000000000000^3107 ≤ 46353169097871^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608571827 10000000000 46353169097871 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3192844607/10000000000 : ℝ)^4131 ≤ (4383242505919/20000000000000 : ℝ)^3107 := by
    have hnat : (3192844607 : ℕ)^4131*20000000000000^3107 ≤ 4383242505919^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3192844607 10000000000 4383242505919 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210873969/500000000 : ℝ), (5608571827/10000000000 : ℝ), (3192844607/10000000000 : ℝ)] ![(31730618367039/100000000000000 : ℝ), (46353169097871/100000000000000 : ℝ), (4383242505919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210873969/500000000 : ℝ)|^4131 ≤ (31730618367039/100000000000000 : ℝ)^3107
        have hw : |(210873969/500000000 : ℝ)|=(210873969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5608571827/10000000000 : ℝ)|^4131 ≤ (46353169097871/100000000000000 : ℝ)^3107
        have hw : |(5608571827/10000000000 : ℝ)|=(5608571827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3192844607/10000000000 : ℝ)|^4131 ≤ (4383242505919/20000000000000 : ℝ)^3107
        have hw : |(3192844607/10000000000 : ℝ)|=(3192844607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28097/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (8261/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8261 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8261*1^2048 ≤ 0^2048*1^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8261/2048 : ℝ) ≤ (310272167663713253/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8261 ≤ (310272167663713253/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8261*12500000000000000000^2048 ≤ 310272167663713253^2048*5^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 310272167663713253 12500000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (310272167663713253/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8261 := by
      have hnat : (1 : ℕ)^2048*1^8261 ≤ 1^8261*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12810272167663713253/12500000000000000000 : ℝ) ≤ (10060969927785073/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (12810272167663713253/12500000000000000000 : ℝ)^2048 ≤ (10060969927785073/10000000000000000 : ℝ)^8261 := by
      have hnat : (12810272167663713253 : ℕ)^2048*10000000000000000^8261 ≤ 10060969927785073^8261*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12810272167663713253 12500000000000000000 10060969927785073 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060969927785073/10000000000000000 : ℝ)) (X := (12810272167663713253/12500000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6560272167663713253/6250000000000000000 : ℝ) ≤ (5060969927785073/5000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (6560272167663713253/6250000000000000000 : ℝ)^2048 ≤ (5060969927785073/5000000000000000 : ℝ)^8261 := by
      have hnat : (6560272167663713253 : ℕ)^2048*5000000000000000^8261 ≤ 5060969927785073^8261*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6560272167663713253 6250000000000000000 5060969927785073 5000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060969927785073/5000000000000000 : ℝ)) (X := (6560272167663713253/6250000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60969927785073/4000000000000000 : ℝ)*(0 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60969927785073/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(310272167663713253/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60969927785073/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (1 : ℝ)+(60969927785073/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060969927785073/10000000000000000 : ℝ) by norm_num, show 1+(310272167663713253/12500000000000000000 : ℝ)+(0 : ℝ)=(12810272167663713253/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(310272167663713253/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60969927785073/4000000000000000 : ℝ)*(2/5 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(60969927785073/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060969927785073/5000000000000000 : ℝ) by norm_num, show 1+2*(310272167663713253/12500000000000000000 : ℝ)=(6560272167663713253/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60969927785073/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60969927785073/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60969927785073/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60969927785073/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60969927785073/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60969927785073/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-239391461/1250000000 : ℝ)*X 0 0+(3035678239/5000000000 : ℝ)*X 0 1+(190846851/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1380225613/2500000000 : ℝ)*X 1 0+(-2663437131/10000000000 : ℝ)*X 1 1+(954234419/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2760453161/5000000000 : ℝ)*X 2 0+(4771170093/10000000000 : ℝ)*X 2 1+(-665858659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206963011/10000000000 : ℝ)*X 0 0+(1562352627/5000000000 : ℝ)*X 0 1+(567440671/1000000000 : ℝ)*X 0 2+(4206963011/10000000000 : ℝ)*X 1 0+(1562352627/5000000000 : ℝ)*X 1 1+(567440671/1000000000 : ℝ)*X 1 2+(4206963011/10000000000 : ℝ)*X 2 0+(1562352627/5000000000 : ℝ)*X 2 1+(567440671/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1920495993/10000000000 : ℝ)*X 0 0+(4804741401/10000000000 : ℝ)*X 0 1+(6036611667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((516799677/1000000000 : ℝ)*X 1 0+(-698999607/5000000000 : ℝ)*X 1 1+(3018304751/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2583998401/5000000000 : ℝ)*X 2 0+(3018305429/5000000000 : ℝ)*X 2 1+(-1397996969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((210873969/500000000 : ℝ)*X 0 0+(5608571827/10000000000 : ℝ)*X 0 1+(3192844607/10000000000 : ℝ)*X 0 2+(210873969/500000000 : ℝ)*X 1 0+(5608571827/10000000000 : ℝ)*X 1 1+(3192844607/10000000000 : ℝ)*X 1 2+(210873969/500000000 : ℝ)*X 2 0+(5608571827/10000000000 : ℝ)*X 2 1+(3192844607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246529752518591437946577/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87641883/50000000000000 : ℝ)*(base1) + (1204231223/100000000000000 : ℝ)*(base19) + (1408181811/100000000000000 : ℝ)*(base23) + (167592179/50000000000000 : ℝ)*(base24) + (43114853/12500000000000 : ℝ)*(upper3) + (290332994528683/50000000000000 : ℝ)*(major0) + (290332994528683/50000000000000 : ℝ)*(major1) + (290332994528683/50000000000000 : ℝ)*(major2) + (76912423408043/10000000000000 : ℝ)*(sp0) + (769124942300407/100000000000000 : ℝ)*(sp1) + (384562201582731/50000000000000 : ℝ)*(sp2) + (196101702142923/50000000000000 : ℝ)*(sp3) + (1043867483/50000000000000 : ℝ)*(sp4) + (1043830159/50000000000000 : ℝ)*(sp7) + (39220566722993/10000000000000 : ℝ)*(f.failure) + (76912614653163/10000000000000 : ℝ)*(f.sum) + (95013049051141/100000000000000000000000000000 : ℝ)*base66 + (103819997451141/200000000000000000000000000000 : ℝ)*base68 + (581015893851141/200000000000000000000000000000 : ℝ)*base70 + (628866864251141/200000000000000000000000000000 : ℝ)*base72 + (153481402448859/100000000000000000000000000000 : ℝ)*base73 + (575105112451141/200000000000000000000000000000 : ℝ)*base76 + (717057424251141/200000000000000000000000000000 : ℝ)*base78 + (966995009451141/200000000000000000000000000000 : ℝ)*base80 + (262440772348859/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (356907/500000000000000000000 : ℝ)*base90 + (356907/500000000000000000000 : ℝ)*base92 + (356907/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (419611780227137662068411/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (443431809/100000000000000 : ℝ)*(base19) + (108362521/25000000000000 : ℝ)*(base23) + (11124389/100000000000000 : ℝ)*(base39) + (373509/1000000000000 : ℝ)*(upper4) + (205918793/100000000000000 : ℝ)*(upper5) + (612864647931923/100000000000000 : ℝ)*(major0) + (612864647931923/100000000000000 : ℝ)*(major1) + (306432318403767/50000000000000 : ℝ)*(major2) + (170122579/25000000000000 : ℝ)*(sp2) + (49779519/25000000000000 : ℝ)*(sp3) + (81177525040203/10000000000000 : ℝ)*(sp4) + (405887403485111/50000000000000 : ℝ)*(sp5) + (811774147586019/100000000000000 : ℝ)*(sp6) + (413953765284047/100000000000000 : ℝ)*(sp7) + (206976982201061/50000000000000 : ℝ)*(f.failure) + (811775261526419/100000000000000 : ℝ)*(f.sum) + (1471880863674639/400000000000000000000000000000 : ℝ)*base66 + (102869368969991/200000000000000000000000000000 : ℝ)*base67 + (1890877920014621/400000000000000000000000000000 : ℝ)*base70 + (1710202917630009/200000000000000000000000000000 : ℝ)*base72 + (744904032725361/400000000000000000000000000000 : ℝ)*base73 + (4777984093614621/400000000000000000000000000000 : ℝ)*base76 + (1863985194814621/400000000000000000000000000000 : ℝ)*base78 + (849986065614621/400000000000000000000000000000 : ℝ)*base80 + (365577140814621/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11531239/2500000000000000000000 : ℝ)*base90 + (11531239/2500000000000000000000 : ℝ)*base92 + (11531239/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1069_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1069_s1_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125054759/10000000000 : ℝ)*x 0 + (2860734783/5000000000 : ℝ)*x 1 + (4986624081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125054759/10000000000 : ℝ)^4131 ≤ (12755158714101/100000000000000 : ℝ)^3107 := by
    have hnat : (2125054759 : ℕ)^4131*100000000000000^3107 ≤ 12755158714101^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125054759 10000000000 12755158714101 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2860734783/5000000000 : ℝ)^4131 ≤ (9519570071489/20000000000000 : ℝ)^3107 := by
    have hnat : (2860734783 : ℕ)^4131*20000000000000^3107 ≤ 9519570071489^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860734783 5000000000 9519570071489 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986624081/10000000000 : ℝ)^4131 ≤ (39646990907827/100000000000000 : ℝ)^3107 := by
    have hnat : (4986624081 : ℕ)^4131*100000000000000^3107 ≤ 39646990907827^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986624081 10000000000 39646990907827 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125054759/10000000000 : ℝ), (2860734783/5000000000 : ℝ), (4986624081/10000000000 : ℝ)] ![(12755158714101/100000000000000 : ℝ), (9519570071489/20000000000000 : ℝ), (39646990907827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125054759/10000000000 : ℝ)|^4131 ≤ (12755158714101/100000000000000 : ℝ)^3107
        have hw : |(-2125054759/10000000000 : ℝ)|=(2125054759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2860734783/5000000000 : ℝ)|^4131 ≤ (9519570071489/20000000000000 : ℝ)^3107
        have hw : |(2860734783/5000000000 : ℝ)|=(2860734783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986624081/10000000000 : ℝ)|^4131 ≤ (39646990907827/100000000000000 : ℝ)^3107
        have hw : |(4986624081/10000000000 : ℝ)|=(4986624081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2711571709/5000000000 : ℝ)*x 0 + (-504625923/2000000000 : ℝ)*x 1 + (4986624393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711571709/5000000000 : ℝ)^4131 ≤ (22163380426509/50000000000000 : ℝ)^3107 := by
    have hnat : (2711571709 : ℕ)^4131*50000000000000^3107 ≤ 22163380426509^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711571709 5000000000 22163380426509 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504625923/2000000000 : ℝ)^4131 ≤ (16026244924547/100000000000000 : ℝ)^3107 := by
    have hnat : (504625923 : ℕ)^4131*100000000000000^3107 ≤ 16026244924547^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504625923 2000000000 16026244924547 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986624393/10000000000 : ℝ)^4131 ≤ (3964699420599/10000000000000 : ℝ)^3107 := by
    have hnat : (4986624393 : ℕ)^4131*10000000000000^3107 ≤ 3964699420599^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986624393 10000000000 3964699420599 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711571709/5000000000 : ℝ), (-504625923/2000000000 : ℝ), (4986624393/10000000000 : ℝ)] ![(22163380426509/50000000000000 : ℝ), (16026244924547/100000000000000 : ℝ), (3964699420599/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711571709/5000000000 : ℝ)|^4131 ≤ (22163380426509/50000000000000 : ℝ)^3107
        have hw : |(2711571709/5000000000 : ℝ)|=(2711571709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-504625923/2000000000 : ℝ)|^4131 ≤ (16026244924547/100000000000000 : ℝ)^3107
        have hw : |(-504625923/2000000000 : ℝ)|=(504625923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986624393/10000000000 : ℝ)|^4131 ≤ (3964699420599/10000000000000 : ℝ)^3107
        have hw : |(4986624393/10000000000 : ℝ)|=(4986624393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2711572013/5000000000 : ℝ)*x 0 + (155831991/312500000 : ℝ)*x 1 + (-504625937/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711572013/5000000000 : ℝ)^4131 ≤ (22163383730223/50000000000000 : ℝ)^3107 := by
    have hnat : (2711572013 : ℕ)^4131*50000000000000^3107 ≤ 22163383730223^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711572013 5000000000 22163383730223 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155831991/312500000 : ℝ)^4131 ≤ (7929397401423/20000000000000 : ℝ)^3107 := by
    have hnat : (155831991 : ℕ)^4131*20000000000000^3107 ≤ 7929397401423^3107*312500000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155831991 312500000 7929397401423 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504625937/2000000000 : ℝ)^4131 ≤ (3205249103141/20000000000000 : ℝ)^3107 := by
    have hnat : (504625937 : ℕ)^4131*20000000000000^3107 ≤ 3205249103141^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504625937 2000000000 3205249103141 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711572013/5000000000 : ℝ), (155831991/312500000 : ℝ), (-504625937/2000000000 : ℝ)] ![(22163383730223/50000000000000 : ℝ), (7929397401423/20000000000000 : ℝ), (3205249103141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711572013/5000000000 : ℝ)|^4131 ≤ (22163383730223/50000000000000 : ℝ)^3107
        have hw : |(2711572013/5000000000 : ℝ)|=(2711572013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155831991/312500000 : ℝ)|^4131 ≤ (7929397401423/20000000000000 : ℝ)^3107
        have hw : |(155831991/312500000 : ℝ)|=(155831991/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-504625937/2000000000 : ℝ)|^4131 ≤ (3205249103141/20000000000000 : ℝ)^3107
        have hw : |(-504625937/2000000000 : ℝ)|=(504625937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080889167/2500000000 : ℝ)*x 0 + (3663140369/10000000000 : ℝ)*x 1 + (510419157/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080889167/2500000000 : ℝ)^4131 ≤ (6559221128267/20000000000000 : ℝ)^3107 := by
    have hnat : (1080889167 : ℕ)^4131*20000000000000^3107 ≤ 6559221128267^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080889167 2500000000 6559221128267 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3663140369/10000000000 : ℝ)^4131 ≤ (13154644989291/50000000000000 : ℝ)^3107 := by
    have hnat : (3663140369 : ℕ)^4131*50000000000000^3107 ≤ 13154644989291^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3663140369 10000000000 13154644989291 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510419157/1000000000 : ℝ)^4131 ≤ (40894604369017/100000000000000 : ℝ)^3107 := by
    have hnat : (510419157 : ℕ)^4131*100000000000000^3107 ≤ 40894604369017^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510419157 1000000000 40894604369017 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080889167/2500000000 : ℝ), (3663140369/10000000000 : ℝ), (510419157/1000000000 : ℝ)] ![(6559221128267/20000000000000 : ℝ), (13154644989291/50000000000000 : ℝ), (40894604369017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080889167/2500000000 : ℝ)|^4131 ≤ (6559221128267/20000000000000 : ℝ)^3107
        have hw : |(1080889167/2500000000 : ℝ)|=(1080889167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3663140369/10000000000 : ℝ)|^4131 ≤ (13154644989291/50000000000000 : ℝ)^3107
        have hw : |(3663140369/10000000000 : ℝ)|=(3663140369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(510419157/1000000000 : ℝ)|^4131 ≤ (40894604369017/100000000000000 : ℝ)^3107
        have hw : |(510419157/1000000000 : ℝ)|=(510419157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-425194429/2000000000 : ℝ)*x 0 + (4996939291/10000000000 : ℝ)*x 1 + (5710942777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425194429/2000000000 : ℝ)^4131 ≤ (12762480426789/100000000000000 : ℝ)^3107 := by
    have hnat : (425194429 : ℕ)^4131*100000000000000^3107 ≤ 12762480426789^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425194429 2000000000 12762480426789 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4996939291/10000000000 : ℝ)^4131 ≤ (7951214102993/20000000000000 : ℝ)^3107 := by
    have hnat : (4996939291 : ℕ)^4131*20000000000000^3107 ≤ 7951214102993^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996939291 10000000000 7951214102993 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5710942777/10000000000 : ℝ)^4131 ≤ (1187036226251/2500000000000 : ℝ)^3107 := by
    have hnat : (5710942777 : ℕ)^4131*2500000000000^3107 ≤ 1187036226251^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710942777 10000000000 1187036226251 2500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425194429/2000000000 : ℝ), (4996939291/10000000000 : ℝ), (5710942777/10000000000 : ℝ)] ![(12762480426789/100000000000000 : ℝ), (7951214102993/20000000000000 : ℝ), (1187036226251/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425194429/2000000000 : ℝ)|^4131 ≤ (12762480426789/100000000000000 : ℝ)^3107
        have hw : |(-425194429/2000000000 : ℝ)|=(425194429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4996939291/10000000000 : ℝ)|^4131 ≤ (7951214102993/20000000000000 : ℝ)^3107
        have hw : |(4996939291/10000000000 : ℝ)|=(4996939291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5710942777/10000000000 : ℝ)|^4131 ≤ (1187036226251/2500000000000 : ℝ)^3107
        have hw : |(5710942777/10000000000 : ℝ)|=(5710942777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5235446013/10000000000 : ℝ)*x 0 + (-1798808931/10000000000 : ℝ)*x 1 + (2855472289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235446013/10000000000 : ℝ)^4131 ≤ (42298688207683/100000000000000 : ℝ)^3107 := by
    have hnat : (5235446013 : ℕ)^4131*100000000000000^3107 ≤ 42298688207683^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235446013 10000000000 42298688207683 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798808931/10000000000 : ℝ)^4131 ≤ (5109921408869/50000000000000 : ℝ)^3107 := by
    have hnat : (1798808931 : ℕ)^4131*50000000000000^3107 ≤ 5109921408869^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798808931 10000000000 5109921408869 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2855472289/5000000000 : ℝ)^4131 ≤ (47481468958783/100000000000000 : ℝ)^3107 := by
    have hnat : (2855472289 : ℕ)^4131*100000000000000^3107 ≤ 47481468958783^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855472289 5000000000 47481468958783 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235446013/10000000000 : ℝ), (-1798808931/10000000000 : ℝ), (2855472289/5000000000 : ℝ)] ![(42298688207683/100000000000000 : ℝ), (5109921408869/50000000000000 : ℝ), (47481468958783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235446013/10000000000 : ℝ)|^4131 ≤ (42298688207683/100000000000000 : ℝ)^3107
        have hw : |(5235446013/10000000000 : ℝ)|=(5235446013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1798808931/10000000000 : ℝ)|^4131 ≤ (5109921408869/50000000000000 : ℝ)^3107
        have hw : |(-1798808931/10000000000 : ℝ)|=(1798808931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2855472289/5000000000 : ℝ)|^4131 ≤ (47481468958783/100000000000000 : ℝ)^3107
        have hw : |(2855472289/5000000000 : ℝ)|=(2855472289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5235443967/10000000000 : ℝ)*x 0 + (2855473421/5000000000 : ℝ)*x 1 + (-112425533/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235443967/10000000000 : ℝ)^4131 ≤ (42298666229451/100000000000000 : ℝ)^3107 := by
    have hnat : (5235443967 : ℕ)^4131*100000000000000^3107 ≤ 42298666229451^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235443967 10000000000 42298666229451 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2855473421/5000000000 : ℝ)^4131 ≤ (5935186748207/12500000000000 : ℝ)^3107 := by
    have hnat : (2855473421 : ℕ)^4131*12500000000000^3107 ≤ 5935186748207^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2855473421 5000000000 5935186748207 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112425533/625000000 : ℝ)^4131 ≤ (10219839773503/100000000000000 : ℝ)^3107 := by
    have hnat : (112425533 : ℕ)^4131*100000000000000^3107 ≤ 10219839773503^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112425533 625000000 10219839773503 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235443967/10000000000 : ℝ), (2855473421/5000000000 : ℝ), (-112425533/625000000 : ℝ)] ![(42298666229451/100000000000000 : ℝ), (5935186748207/12500000000000 : ℝ), (10219839773503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235443967/10000000000 : ℝ)|^4131 ≤ (42298666229451/100000000000000 : ℝ)^3107
        have hw : |(5235443967/10000000000 : ℝ)|=(5235443967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2855473421/5000000000 : ℝ)|^4131 ≤ (5935186748207/12500000000000 : ℝ)^3107
        have hw : |(2855473421/5000000000 : ℝ)|=(2855473421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112425533/625000000 : ℝ)|^4131 ≤ (10219839773503/100000000000000 : ℝ)^3107
        have hw : |(-112425533/625000000 : ℝ)|=(112425533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216267577/500000000 : ℝ)*x 0 + (127098993/250000000 : ℝ)*x 1 + (1841890021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216267577/500000000 : ℝ)^4131 ≤ (32814208962321/100000000000000 : ℝ)^3107 := by
    have hnat : (216267577 : ℕ)^4131*100000000000000^3107 ≤ 32814208962321^3107*500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216267577 500000000 32814208962321 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127098993/250000000 : ℝ)^4131 ≤ (40679224770363/100000000000000 : ℝ)^3107 := by
    have hnat : (127098993 : ℕ)^4131*100000000000000^3107 ≤ 40679224770363^3107*250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127098993 250000000 40679224770363 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1841890021/5000000000 : ℝ)^4131 ≤ (26506566257057/100000000000000 : ℝ)^3107 := by
    have hnat : (1841890021 : ℕ)^4131*100000000000000^3107 ≤ 26506566257057^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841890021 5000000000 26506566257057 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216267577/500000000 : ℝ), (127098993/250000000 : ℝ), (1841890021/5000000000 : ℝ)] ![(32814208962321/100000000000000 : ℝ), (40679224770363/100000000000000 : ℝ), (26506566257057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216267577/500000000 : ℝ)|^4131 ≤ (32814208962321/100000000000000 : ℝ)^3107
        have hw : |(216267577/500000000 : ℝ)|=(216267577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(127098993/250000000 : ℝ)|^4131 ≤ (40679224770363/100000000000000 : ℝ)^3107
        have hw : |(127098993/250000000 : ℝ)|=(127098993/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1841890021/5000000000 : ℝ)|^4131 ≤ (26506566257057/100000000000000 : ℝ)^3107
        have hw : |(1841890021/5000000000 : ℝ)|=(1841890021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_8 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8602197/10000000000 : ℝ)*x 0 + (5489856973/10000000000 : ℝ)*x 1 + (6373174601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8602197/10000000000 : ℝ)^4131 ≤ (8400844331/100000000000000 : ℝ)^3107 := by
    have hnat : (8602197 : ℕ)^4131*100000000000000^3107 ≤ 8400844331^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8602197 10000000000 8400844331 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489856973/10000000000 : ℝ)^4131 ≤ (45053234776469/100000000000000 : ℝ)^3107 := by
    have hnat : (5489856973 : ℕ)^4131*100000000000000^3107 ≤ 45053234776469^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489856973 10000000000 45053234776469 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6373174601/10000000000 : ℝ)^4131 ≤ (10987672872433/20000000000000 : ℝ)^3107 := by
    have hnat : (6373174601 : ℕ)^4131*20000000000000^3107 ≤ 10987672872433^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6373174601 10000000000 10987672872433 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8602197/10000000000 : ℝ), (5489856973/10000000000 : ℝ), (6373174601/10000000000 : ℝ)] ![(8400844331/100000000000000 : ℝ), (45053234776469/100000000000000 : ℝ), (10987672872433/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8602197/10000000000 : ℝ)|^4131 ≤ (8400844331/100000000000000 : ℝ)^3107
        have hw : |(8602197/10000000000 : ℝ)|=(8602197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489856973/10000000000 : ℝ)|^4131 ≤ (45053234776469/100000000000000 : ℝ)^3107
        have hw : |(5489856973/10000000000 : ℝ)|=(5489856973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6373174601/10000000000 : ℝ)|^4131 ≤ (10987672872433/20000000000000 : ℝ)^3107
        have hw : |(6373174601/10000000000 : ℝ)|=(6373174601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_9 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (964563321/10000000000 : ℝ)*x 0 + (-4457027453/10000000000 : ℝ)*x 1 + (3464062893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964563321/10000000000 : ℝ)^4131 ≤ (4462601670019/100000000000000 : ℝ)^3107 := by
    have hnat : (964563321 : ℕ)^4131*100000000000000^3107 ≤ 4462601670019^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964563321 10000000000 4462601670019 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4457027453/10000000000 : ℝ)^4131 ≤ (34149019114813/100000000000000 : ℝ)^3107 := by
    have hnat : (4457027453 : ℕ)^4131*100000000000000^3107 ≤ 34149019114813^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4457027453 10000000000 34149019114813 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3464062893/5000000000 : ℝ)^4131 ≤ (30694189602649/50000000000000 : ℝ)^3107 := by
    have hnat : (3464062893 : ℕ)^4131*50000000000000^3107 ≤ 30694189602649^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3464062893 5000000000 30694189602649 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(964563321/10000000000 : ℝ), (-4457027453/10000000000 : ℝ), (3464062893/5000000000 : ℝ)] ![(4462601670019/100000000000000 : ℝ), (34149019114813/100000000000000 : ℝ), (30694189602649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(964563321/10000000000 : ℝ)|^4131 ≤ (4462601670019/100000000000000 : ℝ)^3107
        have hw : |(964563321/10000000000 : ℝ)|=(964563321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4457027453/10000000000 : ℝ)|^4131 ≤ (34149019114813/100000000000000 : ℝ)^3107
        have hw : |(-4457027453/10000000000 : ℝ)|=(4457027453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3464062893/5000000000 : ℝ)|^4131 ≤ (30694189602649/50000000000000 : ℝ)^3107
        have hw : |(3464062893/5000000000 : ℝ)|=(3464062893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_10 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (482278547/5000000000 : ℝ)*x 0 + (6928112327/10000000000 : ℝ)*x 1 + (-2228523389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482278547/5000000000 : ℝ)^4131 ≤ (178502534621/4000000000000 : ℝ)^3107 := by
    have hnat : (482278547 : ℕ)^4131*4000000000000^3107 ≤ 178502534621^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482278547 5000000000 178502534621 4000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6928112327/10000000000 : ℝ)^4131 ≤ (61388220644071/100000000000000 : ℝ)^3107 := by
    have hnat : (6928112327 : ℕ)^4131*100000000000000^3107 ≤ 61388220644071^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6928112327 10000000000 61388220644071 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228523389/5000000000 : ℝ)^4131 ≤ (17074607989491/50000000000000 : ℝ)^3107 := by
    have hnat : (2228523389 : ℕ)^4131*50000000000000^3107 ≤ 17074607989491^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228523389 5000000000 17074607989491 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(482278547/5000000000 : ℝ), (6928112327/10000000000 : ℝ), (-2228523389/5000000000 : ℝ)] ![(178502534621/4000000000000 : ℝ), (61388220644071/100000000000000 : ℝ), (17074607989491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(482278547/5000000000 : ℝ)|^4131 ≤ (178502534621/4000000000000 : ℝ)^3107
        have hw : |(482278547/5000000000 : ℝ)|=(482278547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6928112327/10000000000 : ℝ)|^4131 ≤ (61388220644071/100000000000000 : ℝ)^3107
        have hw : |(6928112327/10000000000 : ℝ)|=(6928112327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228523389/5000000000 : ℝ)|^4131 ≤ (17074607989491/50000000000000 : ℝ)^3107
        have hw : |(-2228523389/5000000000 : ℝ)|=(2228523389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s1_11 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (481176381/2500000000 : ℝ)*x 0 + (2914880751/5000000000 : ℝ)*x 1 + (2510885221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481176381/2500000000 : ℝ)^4131 ≤ (1118165895161/10000000000000 : ℝ)^3107 := by
    have hnat : (481176381 : ℕ)^4131*10000000000000^3107 ≤ 1118165895161^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481176381 2500000000 1118165895161 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2914880751/5000000000 : ℝ)^4131 ≤ (24399692922053/50000000000000 : ℝ)^3107 := by
    have hnat : (2914880751 : ℕ)^4131*50000000000000^3107 ≤ 24399692922053^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914880751 5000000000 24399692922053 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510885221/5000000000 : ℝ)^4131 ≤ (40018955189389/100000000000000 : ℝ)^3107 := by
    have hnat : (2510885221 : ℕ)^4131*100000000000000^3107 ≤ 40018955189389^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510885221 5000000000 40018955189389 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(481176381/2500000000 : ℝ), (2914880751/5000000000 : ℝ), (2510885221/5000000000 : ℝ)] ![(1118165895161/10000000000000 : ℝ), (24399692922053/50000000000000 : ℝ), (40018955189389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(481176381/2500000000 : ℝ)|^4131 ≤ (1118165895161/10000000000000 : ℝ)^3107
        have hw : |(481176381/2500000000 : ℝ)|=(481176381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2914880751/5000000000 : ℝ)|^4131 ≤ (24399692922053/50000000000000 : ℝ)^3107
        have hw : |(2914880751/5000000000 : ℝ)|=(2914880751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510885221/5000000000 : ℝ)|^4131 ≤ (40018955189389/100000000000000 : ℝ)^3107
        have hw : |(2510885221/5000000000 : ℝ)|=(2510885221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2597/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (109/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (56087067/50000000000000000000 : ℝ) := by
    have hpowers : (109/100000 : ℝ)^8261 ≤ (56087067/50000000000000000000 : ℝ)^2048 := by
      have hnat : (109 : ℕ)^8261*50000000000000000000^2048 ≤ 56087067^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109 100000 56087067 50000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (109/100000 : ℝ)) (X := (56087067/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28097/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (597123803859826111/100000000000000000000 : ℝ) := by
    have hpowers : (28097/100000 : ℝ)^8261 ≤ (597123803859826111/100000000000000000000 : ℝ)^2048 := by
      have hnat : (28097 : ℕ)^8261*100000000000000000000^2048 ≤ 597123803859826111^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28097 100000 597123803859826111 100000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28097/100000 : ℝ)) (X := (597123803859826111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000056087067/25000000000000000000 : ℝ) ≤ (5000000000002781/5000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25000000000056087067/25000000000000000000 : ℝ)^2048 ≤ (5000000000002781/5000000000000000 : ℝ)^8261 := by
      have hnat : (25000000000056087067 : ℕ)^2048*5000000000000000^8261 ≤ 5000000000002781^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000056087067 25000000000000000000 5000000000002781 5000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000002781/5000000000000000 : ℝ)) (X := (25000000000056087067/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20119424760794400049/20000000000000000000 : ℝ) ≤ (1001477028334451/1000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (20119424760794400049/20000000000000000000 : ℝ)^2048 ≤ (1001477028334451/1000000000000000 : ℝ)^8261 := by
      have hnat : (20119424760794400049 : ℕ)^2048*1000000000000000^8261 ≤ 1001477028334451^8261*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20119424760794400049 20000000000000000000 1001477028334451 1000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001477028334451/1000000000000000 : ℝ)) (X := (20119424760794400049/20000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50597123803859826111/50000000000000000000 : ℝ) ≤ (5014770283341729/5000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (50597123803859826111/50000000000000000000 : ℝ)^2048 ≤ (5014770283341729/5000000000000000 : ℝ)^8261 := by
      have hnat : (50597123803859826111 : ℕ)^2048*5000000000000000^8261 ≤ 5014770283341729^8261*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50597123803859826111 50000000000000000000 5014770283341729 5000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014770283341729/5000000000000000 : ℝ)) (X := (50597123803859826111/50000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(56087067/50000000000000000000 : ℝ) ≤ ((8746149377449618081/8746250000000000000 : ℝ)+2*(3692570834737/699700000000000 : ℝ)*(109/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (8746149377449618081/8746250000000000000 : ℝ)+2*(3692570834737/699700000000000 : ℝ)*(109/100000 : ℝ)=(5000000000002781/5000000000000000 : ℝ) by norm_num, show 1+2*(56087067/50000000000000000000 : ℝ)=(25000000000056087067/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(597123803859826111/100000000000000000000 : ℝ)+(56087067/50000000000000000000 : ℝ) ≤ ((8746149377449618081/8746250000000000000 : ℝ)+(3692570834737/699700000000000 : ℝ)*((28097/100000 : ℝ)+(109/100000 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (8746149377449618081/8746250000000000000 : ℝ)+(3692570834737/699700000000000 : ℝ)*((28097/100000 : ℝ)+(109/100000 : ℝ))=(1001477028334451/1000000000000000 : ℝ) by norm_num, show 1+(597123803859826111/100000000000000000000 : ℝ)+(56087067/50000000000000000000 : ℝ)=(20119424760794400049/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(597123803859826111/100000000000000000000 : ℝ) ≤ ((8746149377449618081/8746250000000000000 : ℝ)+2*(3692570834737/699700000000000 : ℝ)*(28097/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (8746149377449618081/8746250000000000000 : ℝ)+2*(3692570834737/699700000000000 : ℝ)*(28097/100000 : ℝ)=(5014770283341729/5000000000000000 : ℝ) by norm_num, show 1+2*(597123803859826111/100000000000000000000 : ℝ)=(50597123803859826111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8746149377449618081/8746250000000000000 : ℝ)*(X 1 0+X 2 0)+(3692570834737/699700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (109/100000 : ℝ)) (hi := (28097/100000 : ℝ)) (c := (8746149377449618081/8746250000000000000 : ℝ)) (alpha := (3692570834737/699700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8746149377449618081/8746250000000000000 : ℝ)*(X 0 1+X 2 1)+(3692570834737/699700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (109/100000 : ℝ)) (hi := (28097/100000 : ℝ)) (c := (8746149377449618081/8746250000000000000 : ℝ)) (alpha := (3692570834737/699700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8746149377449618081/8746250000000000000 : ℝ)*(X 0 2+X 1 2)+(3692570834737/699700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (109/100000 : ℝ)) (hi := (28097/100000 : ℝ)) (c := (8746149377449618081/8746250000000000000 : ℝ)) (alpha := (3692570834737/699700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2125054759/10000000000 : ℝ)*X 0 0+(2860734783/5000000000 : ℝ)*X 0 1+(4986624081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711571709/5000000000 : ℝ)*X 1 0+(-504625923/2000000000 : ℝ)*X 1 1+(4986624393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711572013/5000000000 : ℝ)*X 2 0+(155831991/312500000 : ℝ)*X 2 1+(-504625937/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080889167/2500000000 : ℝ)*X 0 0+(3663140369/10000000000 : ℝ)*X 0 1+(510419157/1000000000 : ℝ)*X 0 2+(1080889167/2500000000 : ℝ)*X 1 0+(3663140369/10000000000 : ℝ)*X 1 1+(510419157/1000000000 : ℝ)*X 1 2+(1080889167/2500000000 : ℝ)*X 2 0+(3663140369/10000000000 : ℝ)*X 2 1+(510419157/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-425194429/2000000000 : ℝ)*X 0 0+(4996939291/10000000000 : ℝ)*X 0 1+(5710942777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5235446013/10000000000 : ℝ)*X 1 0+(-1798808931/10000000000 : ℝ)*X 1 1+(2855472289/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5235443967/10000000000 : ℝ)*X 2 0+(2855473421/5000000000 : ℝ)*X 2 1+(-112425533/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216267577/500000000 : ℝ)*X 0 0+(127098993/250000000 : ℝ)*X 0 1+(1841890021/5000000000 : ℝ)*X 0 2+(216267577/500000000 : ℝ)*X 1 0+(127098993/250000000 : ℝ)*X 1 1+(1841890021/5000000000 : ℝ)*X 1 2+(216267577/500000000 : ℝ)*X 2 0+(127098993/250000000 : ℝ)*X 2 1+(1841890021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((8602197/10000000000 : ℝ)*X 0 0+(5489856973/10000000000 : ℝ)*X 0 1+(6373174601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((964563321/10000000000 : ℝ)*X 1 0+(-4457027453/10000000000 : ℝ)*X 1 1+(3464062893/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((482278547/5000000000 : ℝ)*X 2 0+(6928112327/10000000000 : ℝ)*X 2 1+(-2228523389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((481176381/2500000000 : ℝ)*X 0 0+(2914880751/5000000000 : ℝ)*X 0 1+(2510885221/5000000000 : ℝ)*X 0 2+(481176381/2500000000 : ℝ)*X 1 0+(2914880751/5000000000 : ℝ)*X 1 1+(2510885221/5000000000 : ℝ)*X 1 2+(481176381/2500000000 : ℝ)*X 2 0+(2914880751/5000000000 : ℝ)*X 2 1+(2510885221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (969810022968203862847274553/109328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (513693600574421/50000000000000 : ℝ)*(major0) + (513693600574421/50000000000000 : ℝ)*(major1) + (513693600574421/50000000000000 : ℝ)*(major2) + (170104052675059/12500000000000 : ℝ)*(sp0) + (680416585100383/50000000000000 : ℝ)*(sp1) + (1360832309623303/100000000000000 : ℝ)*(sp2) + (4337115093199/625000000000 : ℝ)*(sp3) + (136204887/10000000000000 : ℝ)*(sp4) + (878734227/100000000000000 : ℝ)*(sp5) + (1583407061/100000000000000 : ℝ)*(sp6) + (794544019/100000000000000 : ℝ)*(sp8) + (8266537/1562500000000 : ℝ)*(sp9) + (684962997/100000000000000 : ℝ)*(sp10) + (34803269/3125000000000 : ℝ)*(sp11) + (1355350641829/195312500000 : ℝ)*(f.failure) + (1360834577993361/100000000000000 : ℝ)*(f.sum) + (97247934454591/34985000000000000000000000000 : ℝ)*base66 + (188234965568356101/437312500000000000000000000000000 : ℝ)*base67 + (623974254520643899/437312500000000000000000000000000 : ℝ)*base70 + (100355422182768899/437312500000000000000000000000000 : ℝ)*base72 + (74311278244771/34985000000000000000000000000 : ℝ)*base74 + (858677184236081399/437312500000000000000000000000000 : ℝ)*base76 + (594594777748518899/437312500000000000000000000000000 : ℝ)*base78 + (129601707561393899/437312500000000000000000000000000 : ℝ)*base80 + (84373631128841/34985000000000000000000000000 : ℝ)*base82 + (91133/19531250000000000000 : ℝ)*base89 + (91133/19531250000000000000 : ℝ)*base91 + (91133/19531250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122281276926141111753303/34985000000000000000000000000 : ℝ) := by norm_num
    linear_combination (238520989/100000000000000 : ℝ)*(lower4) + (891413/25000000000000 : ℝ)*(upper5) + (1057373610481593/100000000000000 : ℝ)*(major0) + (1057373610481593/100000000000000 : ℝ)*(major1) + (1057373610481593/100000000000000 : ℝ)*(major2) + (1358805147/100000000000000 : ℝ)*(sp0) + (1658810993/100000000000000 : ℝ)*(sp1) + (2108888881/50000000000000 : ℝ)*(sp2) + (140054868330079/10000000000000 : ℝ)*(sp4) + (350137966023/25000000000 : ℝ)*(sp5) + (87534331570327/6250000000000 : ℝ)*(sp6) + (178548115158423/25000000000000 : ℝ)*(sp7) + (27193727/781250000000 : ℝ)*(sp8) + (560459101/50000000000000 : ℝ)*(sp11) + (357096790775947/50000000000000 : ℝ)*(f.failure) + (700276761451497/50000000000000 : ℝ)*(f.sum) + (8036761100601/8746250000000000000000000000 : ℝ)*base66 + (529741936010004467/874625000000000000000000000000000 : ℝ)*base68 + (3456745884308870533/874625000000000000000000000000000 : ℝ)*base69 + (1159324787131745533/874625000000000000000000000000000 : ℝ)*base71 + (14703236044931/8746250000000000000000000000 : ℝ)*base74 + (4993536478379870533/874625000000000000000000000000000 : ℝ)*base75 + (1797463171462504467/874625000000000000000000000000000 : ℝ)*base78 + (1189158727144504467/874625000000000000000000000000000 : ℝ)*base80 + (90955009379271/34985000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (14386153/2500000000000000000000 : ℝ)*base90 + (14386153/2500000000000000000000 : ℝ)*base92 + (14386153/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1069_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2597/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1069_s2_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091152471/5000000000 : ℝ)*x 0 + (5525273063/10000000000 : ℝ)*x 1 + (2573247507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091152471/5000000000 : ℝ)^4131 ≤ (13214059628633/100000000000000 : ℝ)^3107 := by
    have hnat : (1091152471 : ℕ)^4131*100000000000000^3107 ≤ 13214059628633^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091152471 5000000000 13214059628633 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5525273063/10000000000 : ℝ)^4131 ≤ (1817603308591/4000000000000 : ℝ)^3107 := by
    have hnat : (5525273063 : ℕ)^4131*4000000000000^3107 ≤ 1817603308591^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525273063 10000000000 1817603308591 4000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2573247507/5000000000 : ℝ)^4131 ≤ (41345857637491/100000000000000 : ℝ)^3107 := by
    have hnat : (2573247507 : ℕ)^4131*100000000000000^3107 ≤ 41345857637491^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573247507 5000000000 41345857637491 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091152471/5000000000 : ℝ), (5525273063/10000000000 : ℝ), (2573247507/5000000000 : ℝ)] ![(13214059628633/100000000000000 : ℝ), (1817603308591/4000000000000 : ℝ), (41345857637491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091152471/5000000000 : ℝ)|^4131 ≤ (13214059628633/100000000000000 : ℝ)^3107
        have hw : |(-1091152471/5000000000 : ℝ)|=(1091152471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5525273063/10000000000 : ℝ)|^4131 ≤ (1817603308591/4000000000000 : ℝ)^3107
        have hw : |(5525273063/10000000000 : ℝ)|=(5525273063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2573247507/5000000000 : ℝ)|^4131 ≤ (41345857637491/100000000000000 : ℝ)^3107
        have hw : |(2573247507/5000000000 : ℝ)|=(2573247507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377066491/10000000000 : ℝ)*x 0 + (-297476821/1250000000 : ℝ)*x 1 + (5146496131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377066491/10000000000 : ℝ)^4131 ≤ (5478340399613/12500000000000 : ℝ)^3107 := by
    have hnat : (5377066491 : ℕ)^4131*12500000000000^3107 ≤ 5478340399613^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377066491 10000000000 5478340399613 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297476821/1250000000 : ℝ)^4131 ≤ (3706851804601/25000000000000 : ℝ)^3107 := by
    have hnat : (297476821 : ℕ)^4131*25000000000000^3107 ≤ 3706851804601^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297476821 1250000000 3706851804601 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5146496131/10000000000 : ℝ)^4131 ≤ (20672934784393/50000000000000 : ℝ)^3107 := by
    have hnat : (5146496131 : ℕ)^4131*50000000000000^3107 ≤ 20672934784393^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146496131 10000000000 20672934784393 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377066491/10000000000 : ℝ), (-297476821/1250000000 : ℝ), (5146496131/10000000000 : ℝ)] ![(5478340399613/12500000000000 : ℝ), (3706851804601/25000000000000 : ℝ), (20672934784393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377066491/10000000000 : ℝ)|^4131 ≤ (5478340399613/12500000000000 : ℝ)^3107
        have hw : |(5377066491/10000000000 : ℝ)|=(5377066491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297476821/1250000000 : ℝ)|^4131 ≤ (3706851804601/25000000000000 : ℝ)^3107
        have hw : |(-297476821/1250000000 : ℝ)|=(297476821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5146496131/10000000000 : ℝ)|^4131 ≤ (20672934784393/50000000000000 : ℝ)^3107
        have hw : |(5146496131/10000000000 : ℝ)|=(5146496131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688533143/5000000000 : ℝ)*x 0 + (321656023/625000000 : ℝ)*x 1 + (-2379814531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688533143/5000000000 : ℝ)^4131 ≤ (43826720975327/100000000000000 : ℝ)^3107 := by
    have hnat : (2688533143 : ℕ)^4131*100000000000000^3107 ≤ 43826720975327^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688533143 5000000000 43826720975327 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321656023/625000000 : ℝ)^4131 ≤ (20672936050157/50000000000000 : ℝ)^3107 := by
    have hnat : (321656023 : ℕ)^4131*50000000000000^3107 ≤ 20672936050157^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321656023 625000000 20672936050157 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2379814531/10000000000 : ℝ)^4131 ≤ (14827406911899/100000000000000 : ℝ)^3107 := by
    have hnat : (2379814531 : ℕ)^4131*100000000000000^3107 ≤ 14827406911899^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379814531 10000000000 14827406911899 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688533143/5000000000 : ℝ), (321656023/625000000 : ℝ), (-2379814531/10000000000 : ℝ)] ![(43826720975327/100000000000000 : ℝ), (20672936050157/50000000000000 : ℝ), (14827406911899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688533143/5000000000 : ℝ)|^4131 ≤ (43826720975327/100000000000000 : ℝ)^3107
        have hw : |(2688533143/5000000000 : ℝ)|=(2688533143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321656023/625000000 : ℝ)|^4131 ≤ (20672936050157/50000000000000 : ℝ)^3107
        have hw : |(321656023/625000000 : ℝ)|=(321656023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2379814531/10000000000 : ℝ)|^4131 ≤ (14827406911899/100000000000000 : ℝ)^3107
        have hw : |(-2379814531/10000000000 : ℝ)|=(2379814531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4362633131/10000000000 : ℝ)*x 0 + (4007167649/10000000000 : ℝ)*x 1 + (2374975709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362633131/10000000000 : ℝ)^4131 ≤ (16595397471289/50000000000000 : ℝ)^3107 := by
    have hnat : (4362633131 : ℕ)^4131*50000000000000^3107 ≤ 16595397471289^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362633131 10000000000 16595397471289 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007167649/10000000000 : ℝ)^4131 ≤ (14822155017887/50000000000000 : ℝ)^3107 := by
    have hnat : (4007167649 : ℕ)^4131*50000000000000^3107 ≤ 14822155017887^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007167649 10000000000 14822155017887 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2374975709/5000000000 : ℝ)^4131 ≤ (18582447500689/50000000000000 : ℝ)^3107 := by
    have hnat : (2374975709 : ℕ)^4131*50000000000000^3107 ≤ 18582447500689^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374975709 5000000000 18582447500689 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362633131/10000000000 : ℝ), (4007167649/10000000000 : ℝ), (2374975709/5000000000 : ℝ)] ![(16595397471289/50000000000000 : ℝ), (14822155017887/50000000000000 : ℝ), (18582447500689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362633131/10000000000 : ℝ)|^4131 ≤ (16595397471289/50000000000000 : ℝ)^3107
        have hw : |(4362633131/10000000000 : ℝ)|=(4362633131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007167649/10000000000 : ℝ)|^4131 ≤ (14822155017887/50000000000000 : ℝ)^3107
        have hw : |(4007167649/10000000000 : ℝ)|=(4007167649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2374975709/5000000000 : ℝ)|^4131 ≤ (18582447500689/50000000000000 : ℝ)^3107
        have hw : |(2374975709/5000000000 : ℝ)|=(2374975709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-436485899/2000000000 : ℝ)*x 0 + (5149246187/10000000000 : ℝ)*x 1 + (5522493363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436485899/2000000000 : ℝ)^4131 ≤ (13215062379497/100000000000000 : ℝ)^3107 := by
    have hnat : (436485899 : ℕ)^4131*100000000000000^3107 ≤ 13215062379497^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436485899 2000000000 13215062379497 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149246187/10000000000 : ℝ)^4131 ≤ (41375247025489/100000000000000 : ℝ)^3107 := by
    have hnat : (5149246187 : ℕ)^4131*100000000000000^3107 ≤ 41375247025489^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149246187 10000000000 41375247025489 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522493363/10000000000 : ℝ)^4131 ≤ (11352422644659/25000000000000 : ℝ)^3107 := by
    have hnat : (5522493363 : ℕ)^4131*25000000000000^3107 ≤ 11352422644659^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522493363 10000000000 11352422644659 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436485899/2000000000 : ℝ), (5149246187/10000000000 : ℝ), (5522493363/10000000000 : ℝ)] ![(13215062379497/100000000000000 : ℝ), (41375247025489/100000000000000 : ℝ), (11352422644659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436485899/2000000000 : ℝ)|^4131 ≤ (13215062379497/100000000000000 : ℝ)^3107
        have hw : |(-436485899/2000000000 : ℝ)|=(436485899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149246187/10000000000 : ℝ)|^4131 ≤ (41375247025489/100000000000000 : ℝ)^3107
        have hw : |(5149246187/10000000000 : ℝ)|=(5149246187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522493363/10000000000 : ℝ)|^4131 ≤ (11352422644659/25000000000000 : ℝ)^3107
        have hw : |(5522493363/10000000000 : ℝ)|=(5522493363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330089903/625000000 : ℝ)*x 0 + (-2003819119/10000000000 : ℝ)*x 1 + (5522493451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330089903/625000000 : ℝ)^4131 ≤ (42793455041057/100000000000000 : ℝ)^3107 := by
    have hnat : (330089903 : ℕ)^4131*100000000000000^3107 ≤ 42793455041057^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330089903 625000000 42793455041057 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003819119/10000000000 : ℝ)^4131 ≤ (11796853406747/100000000000000 : ℝ)^3107 := by
    have hnat : (2003819119 : ℕ)^4131*100000000000000^3107 ≤ 11796853406747^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003819119 10000000000 11796853406747 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522493451/10000000000 : ℝ)^4131 ≤ (45409691540713/100000000000000 : ℝ)^3107 := by
    have hnat : (5522493451 : ℕ)^4131*100000000000000^3107 ≤ 45409691540713^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522493451 10000000000 45409691540713 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330089903/625000000 : ℝ), (-2003819119/10000000000 : ℝ), (5522493451/10000000000 : ℝ)] ![(42793455041057/100000000000000 : ℝ), (11796853406747/100000000000000 : ℝ), (45409691540713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330089903/625000000 : ℝ)|^4131 ≤ (42793455041057/100000000000000 : ℝ)^3107
        have hw : |(330089903/625000000 : ℝ)|=(330089903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2003819119/10000000000 : ℝ)|^4131 ≤ (11796853406747/100000000000000 : ℝ)^3107
        have hw : |(-2003819119/10000000000 : ℝ)|=(2003819119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522493451/10000000000 : ℝ)|^4131 ≤ (45409691540713/100000000000000 : ℝ)^3107
        have hw : |(5522493451/10000000000 : ℝ)|=(5522493451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1320359673/2500000000 : ℝ)*x 0 + (690311661/1250000000 : ℝ)*x 1 + (-200381901/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320359673/2500000000 : ℝ)^4131 ≤ (42793457669683/100000000000000 : ℝ)^3107 := by
    have hnat : (1320359673 : ℕ)^4131*100000000000000^3107 ≤ 42793457669683^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320359673 2500000000 42793457669683 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690311661/1250000000 : ℝ)^4131 ≤ (11352422439671/25000000000000 : ℝ)^3107 := by
    have hnat : (690311661 : ℕ)^4131*25000000000000^3107 ≤ 11352422439671^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690311661 1250000000 11352422439671 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200381901/1000000000 : ℝ)^4131 ≤ (737303284597/6250000000000 : ℝ)^3107 := by
    have hnat : (200381901 : ℕ)^4131*6250000000000^3107 ≤ 737303284597^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200381901 1000000000 737303284597 6250000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320359673/2500000000 : ℝ), (690311661/1250000000 : ℝ), (-200381901/1000000000 : ℝ)] ![(42793457669683/100000000000000 : ℝ), (11352422439671/25000000000000 : ℝ), (737303284597/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320359673/2500000000 : ℝ)|^4131 ≤ (42793457669683/100000000000000 : ℝ)^3107
        have hw : |(1320359673/2500000000 : ℝ)|=(1320359673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(690311661/1250000000 : ℝ)|^4131 ≤ (11352422439671/25000000000000 : ℝ)^3107
        have hw : |(690311661/1250000000 : ℝ)|=(690311661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200381901/1000000000 : ℝ)|^4131 ≤ (737303284597/6250000000000 : ℝ)^3107
        have hw : |(-200381901/1000000000 : ℝ)|=(200381901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545359401/1250000000 : ℝ)*x 0 + (593070433/1250000000 : ℝ)*x 1 + (80252299/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545359401/1250000000 : ℝ)^4131 ≤ (16596621834881/50000000000000 : ℝ)^3107 := by
    have hnat : (545359401 : ℕ)^4131*50000000000000^3107 ≤ 16596621834881^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545359401 1250000000 16596621834881 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593070433/1250000000 : ℝ)^4131 ≤ (37108854713771/100000000000000 : ℝ)^3107 := by
    have hnat : (593070433 : ℕ)^4131*100000000000000^3107 ≤ 37108854713771^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593070433 1250000000 37108854713771 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80252299/200000000 : ℝ)^4131 ≤ (14848950797729/50000000000000 : ℝ)^3107 := by
    have hnat : (80252299 : ℕ)^4131*50000000000000^3107 ≤ 14848950797729^3107*200000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80252299 200000000 14848950797729 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545359401/1250000000 : ℝ), (593070433/1250000000 : ℝ), (80252299/200000000 : ℝ)] ![(16596621834881/50000000000000 : ℝ), (37108854713771/100000000000000 : ℝ), (14848950797729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545359401/1250000000 : ℝ)|^4131 ≤ (16596621834881/50000000000000 : ℝ)^3107
        have hw : |(545359401/1250000000 : ℝ)|=(545359401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(593070433/1250000000 : ℝ)|^4131 ≤ (37108854713771/100000000000000 : ℝ)^3107
        have hw : |(593070433/1250000000 : ℝ)|=(593070433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80252299/200000000 : ℝ)|^4131 ≤ (14848950797729/50000000000000 : ℝ)^3107
        have hw : |(80252299/200000000 : ℝ)|=(80252299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_8 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99426241/10000000000 : ℝ)*x 0 + (2963843811/5000000000 : ℝ)*x 1 + (5927503499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99426241/10000000000 : ℝ)^4131 ≤ (217530755367/100000000000000 : ℝ)^3107 := by
    have hnat : (99426241 : ℕ)^4131*100000000000000^3107 ≤ 217530755367^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99426241 10000000000 217530755367 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2963843811/5000000000 : ℝ)^4131 ≤ (49892264850709/100000000000000 : ℝ)^3107 := by
    have hnat : (2963843811 : ℕ)^4131*100000000000000^3107 ≤ 49892264850709^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963843811 5000000000 49892264850709 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5927503499/10000000000 : ℝ)^4131 ≤ (24945102187091/50000000000000 : ℝ)^3107 := by
    have hnat : (5927503499 : ℕ)^4131*50000000000000^3107 ≤ 24945102187091^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5927503499 10000000000 24945102187091 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99426241/10000000000 : ℝ), (2963843811/5000000000 : ℝ), (5927503499/10000000000 : ℝ)] ![(217530755367/100000000000000 : ℝ), (49892264850709/100000000000000 : ℝ), (24945102187091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99426241/10000000000 : ℝ)|^4131 ≤ (217530755367/100000000000000 : ℝ)^3107
        have hw : |(-99426241/10000000000 : ℝ)|=(99426241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2963843811/5000000000 : ℝ)|^4131 ≤ (49892264850709/100000000000000 : ℝ)^3107
        have hw : |(2963843811/5000000000 : ℝ)|=(2963843811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5927503499/10000000000 : ℝ)|^4131 ≤ (24945102187091/50000000000000 : ℝ)^3107
        have hw : |(5927503499/10000000000 : ℝ)|=(5927503499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_9 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (794604719/10000000000 : ℝ)*x 0 + (-496963507/1000000000 : ℝ)*x 1 + (163986653/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (794604719/10000000000 : ℝ)^4131 ≤ (689754812787/20000000000000 : ℝ)^3107 := by
    have hnat : (794604719 : ℕ)^4131*20000000000000^3107 ≤ 689754812787^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794604719 10000000000 689754812787 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496963507/1000000000 : ℝ)^4131 ≤ (19733750184121/50000000000000 : ℝ)^3107 := by
    have hnat : (496963507 : ℕ)^4131*50000000000000^3107 ≤ 19733750184121^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496963507 1000000000 19733750184121 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163986653/250000000 : ℝ)^4131 ≤ (11416745111373/20000000000000 : ℝ)^3107 := by
    have hnat : (163986653 : ℕ)^4131*20000000000000^3107 ≤ 11416745111373^3107*250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163986653 250000000 11416745111373 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(794604719/10000000000 : ℝ), (-496963507/1000000000 : ℝ), (163986653/250000000 : ℝ)] ![(689754812787/20000000000000 : ℝ), (19733750184121/50000000000000 : ℝ), (11416745111373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(794604719/10000000000 : ℝ)|^4131 ≤ (689754812787/20000000000000 : ℝ)^3107
        have hw : |(794604719/10000000000 : ℝ)|=(794604719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496963507/1000000000 : ℝ)|^4131 ≤ (19733750184121/50000000000000 : ℝ)^3107
        have hw : |(-496963507/1000000000 : ℝ)|=(496963507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163986653/250000000 : ℝ)|^4131 ≤ (11416745111373/20000000000000 : ℝ)^3107
        have hw : |(163986653/250000000 : ℝ)|=(163986653/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_10 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (15864657/200000000 : ℝ)*x 0 + (3277966809/5000000000 : ℝ)*x 1 + (-4974254439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15864657/200000000 : ℝ)^4131 ≤ (3440859690037/100000000000000 : ℝ)^3107 := by
    have hnat : (15864657 : ℕ)^4131*100000000000000^3107 ≤ 3440859690037^3107*200000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15864657 200000000 3440859690037 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3277966809/5000000000 : ℝ)^4131 ≤ (57042855840223/100000000000000 : ℝ)^3107 := by
    have hnat : (3277966809 : ℕ)^4131*100000000000000^3107 ≤ 57042855840223^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3277966809 5000000000 57042855840223 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4974254439/10000000000 : ℝ)^4131 ≤ (39516284460027/100000000000000 : ℝ)^3107 := by
    have hnat : (4974254439 : ℕ)^4131*100000000000000^3107 ≤ 39516284460027^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974254439 10000000000 39516284460027 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(15864657/200000000 : ℝ), (3277966809/5000000000 : ℝ), (-4974254439/10000000000 : ℝ)] ![(3440859690037/100000000000000 : ℝ), (57042855840223/100000000000000 : ℝ), (39516284460027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(15864657/200000000 : ℝ)|^4131 ≤ (3440859690037/100000000000000 : ℝ)^3107
        have hw : |(15864657/200000000 : ℝ)|=(15864657/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3277966809/5000000000 : ℝ)|^4131 ≤ (57042855840223/100000000000000 : ℝ)^3107
        have hw : |(3277966809/5000000000 : ℝ)|=(3277966809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4974254439/10000000000 : ℝ)|^4131 ≤ (39516284460027/100000000000000 : ℝ)^3107
        have hw : |(-4974254439/10000000000 : ℝ)|=(4974254439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s2_11 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52512933/1250000000 : ℝ)*x 0 + (2934625521/5000000000 : ℝ)*x 1 + (1174627397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52512933/1250000000 : ℝ)^4131 ≤ (738948659943/50000000000000 : ℝ)^3107 := by
    have hnat : (52512933 : ℕ)^4131*50000000000000^3107 ≤ 738948659943^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52512933 1250000000 738948659943 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2934625521/5000000000 : ℝ)^4131 ≤ (49239376408501/100000000000000 : ℝ)^3107 := by
    have hnat : (2934625521 : ℕ)^4131*100000000000000^3107 ≤ 49239376408501^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934625521 5000000000 49239376408501 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174627397/2000000000 : ℝ)^4131 ≤ (9856545251719/20000000000000 : ℝ)^3107 := by
    have hnat : (1174627397 : ℕ)^4131*20000000000000^3107 ≤ 9856545251719^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174627397 2000000000 9856545251719 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52512933/1250000000 : ℝ), (2934625521/5000000000 : ℝ), (1174627397/2000000000 : ℝ)] ![(738948659943/50000000000000 : ℝ), (49239376408501/100000000000000 : ℝ), (9856545251719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52512933/1250000000 : ℝ)|^4131 ≤ (738948659943/50000000000000 : ℝ)^3107
        have hw : |(52512933/1250000000 : ℝ)|=(52512933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2934625521/5000000000 : ℝ)|^4131 ≤ (49239376408501/100000000000000 : ℝ)^3107
        have hw : |(2934625521/5000000000 : ℝ)|=(2934625521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1174627397/2000000000 : ℝ)|^4131 ≤ (9856545251719/20000000000000 : ℝ)^3107
        have hw : |(1174627397/2000000000 : ℝ)|=(1174627397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2597/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8727/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16731/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2597/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2597/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2597/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2597/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2597/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2597/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5231/100000 : ℝ) ^ (8261/2048 : ℝ) ≤ (338950439733823/50000000000000000000 : ℝ) := by
    have hpowers : (5231/100000 : ℝ)^8261 ≤ (338950439733823/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5231 : ℕ)^8261*50000000000000000000^2048 ≤ 338950439733823^2048*100000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5231 100000 338950439733823 50000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5231/100000 : ℝ)) (X := (338950439733823/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2597/12500 : ℝ) ^ (8261/2048 : ℝ) ≤ (176707689520100689/100000000000000000000 : ℝ) := by
    have hpowers : (2597/12500 : ℝ)^8261 ≤ (176707689520100689/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2597 : ℕ)^8261*100000000000000000000^2048 ≤ 176707689520100689^2048*12500^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2597 12500 176707689520100689 100000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2597/12500 : ℝ)) (X := (176707689520100689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000338950439733823/25000000000000000000 : ℝ) ≤ (10000033611764263/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25000338950439733823/25000000000000000000 : ℝ)^2048 ≤ (10000033611764263/10000000000000000 : ℝ)^8261 := by
      have hnat : (25000338950439733823 : ℕ)^2048*10000000000000000^8261 ≤ 10000033611764263^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000338950439733823 25000000000000000000 10000033611764263 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000033611764263/10000000000000000 : ℝ)) (X := (25000338950439733823/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20035477118079913667/20000000000000000000 : ℝ) ≤ (5002197334529089/5000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (20035477118079913667/20000000000000000000 : ℝ)^2048 ≤ (5002197334529089/5000000000000000 : ℝ)^8261 := by
      have hnat : (20035477118079913667 : ℕ)^2048*5000000000000000^8261 ≤ 5002197334529089^8261*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20035477118079913667 20000000000000000000 5002197334529089 5000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002197334529089/5000000000000000 : ℝ)) (X := (20035477118079913667/20000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50176707689520100689/50000000000000000000 : ℝ) ≤ (10008755726352093/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (50176707689520100689/50000000000000000000 : ℝ)^2048 ≤ (10008755726352093/10000000000000000 : ℝ)^8261 := by
      have hnat : (50176707689520100689 : ℕ)^2048*10000000000000000^8261 ≤ 10008755726352093^8261*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50176707689520100689 50000000000000000000 10008755726352093 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008755726352093/10000000000000000 : ℝ)) (X := (50176707689520100689/50000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(338950439733823/50000000000000000000 : ℝ) ≤ ((31080979422693305921/31090000000000000000 : ℝ)+2*(872211458783/310900000000000 : ℝ)*(5231/100000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (31080979422693305921/31090000000000000000 : ℝ)+2*(872211458783/310900000000000 : ℝ)*(5231/100000 : ℝ)=(10000033611764263/10000000000000000 : ℝ) by norm_num, show 1+2*(338950439733823/50000000000000000000 : ℝ)=(25000338950439733823/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(176707689520100689/100000000000000000000 : ℝ)+(338950439733823/50000000000000000000 : ℝ) ≤ ((31080979422693305921/31090000000000000000 : ℝ)+(872211458783/310900000000000 : ℝ)*((2597/12500 : ℝ)+(5231/100000 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (31080979422693305921/31090000000000000000 : ℝ)+(872211458783/310900000000000 : ℝ)*((2597/12500 : ℝ)+(5231/100000 : ℝ))=(5002197334529089/5000000000000000 : ℝ) by norm_num, show 1+(176707689520100689/100000000000000000000 : ℝ)+(338950439733823/50000000000000000000 : ℝ)=(20035477118079913667/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(176707689520100689/100000000000000000000 : ℝ) ≤ ((31080979422693305921/31090000000000000000 : ℝ)+2*(872211458783/310900000000000 : ℝ)*(2597/12500 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (31080979422693305921/31090000000000000000 : ℝ)+2*(872211458783/310900000000000 : ℝ)*(2597/12500 : ℝ)=(10008755726352093/10000000000000000 : ℝ) by norm_num, show 1+2*(176707689520100689/100000000000000000000 : ℝ)=(50176707689520100689/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31080979422693305921/31090000000000000000 : ℝ)*(X 1 0+X 2 0)+(872211458783/310900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5231/100000 : ℝ)) (hi := (2597/12500 : ℝ)) (c := (31080979422693305921/31090000000000000000 : ℝ)) (alpha := (872211458783/310900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31080979422693305921/31090000000000000000 : ℝ)*(X 0 1+X 2 1)+(872211458783/310900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5231/100000 : ℝ)) (hi := (2597/12500 : ℝ)) (c := (31080979422693305921/31090000000000000000 : ℝ)) (alpha := (872211458783/310900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31080979422693305921/31090000000000000000 : ℝ)*(X 0 2+X 1 2)+(872211458783/310900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (5231/100000 : ℝ)) (hi := (2597/12500 : ℝ)) (c := (31080979422693305921/31090000000000000000 : ℝ)) (alpha := (872211458783/310900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1091152471/5000000000 : ℝ)*X 0 0+(5525273063/10000000000 : ℝ)*X 0 1+(2573247507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377066491/10000000000 : ℝ)*X 1 0+(-297476821/1250000000 : ℝ)*X 1 1+(5146496131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688533143/5000000000 : ℝ)*X 2 0+(321656023/625000000 : ℝ)*X 2 1+(-2379814531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362633131/10000000000 : ℝ)*X 0 0+(4007167649/10000000000 : ℝ)*X 0 1+(2374975709/5000000000 : ℝ)*X 0 2+(4362633131/10000000000 : ℝ)*X 1 0+(4007167649/10000000000 : ℝ)*X 1 1+(2374975709/5000000000 : ℝ)*X 1 2+(4362633131/10000000000 : ℝ)*X 2 0+(4007167649/10000000000 : ℝ)*X 2 1+(2374975709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-436485899/2000000000 : ℝ)*X 0 0+(5149246187/10000000000 : ℝ)*X 0 1+(5522493363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330089903/625000000 : ℝ)*X 1 0+(-2003819119/10000000000 : ℝ)*X 1 1+(5522493451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1320359673/2500000000 : ℝ)*X 2 0+(690311661/1250000000 : ℝ)*X 2 1+(-200381901/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545359401/1250000000 : ℝ)*X 0 0+(593070433/1250000000 : ℝ)*X 0 1+(80252299/200000000 : ℝ)*X 0 2+(545359401/1250000000 : ℝ)*X 1 0+(593070433/1250000000 : ℝ)*X 1 1+(80252299/200000000 : ℝ)*X 1 2+(545359401/1250000000 : ℝ)*X 2 0+(593070433/1250000000 : ℝ)*X 2 1+(80252299/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-99426241/10000000000 : ℝ)*X 0 0+(2963843811/5000000000 : ℝ)*X 0 1+(5927503499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((794604719/10000000000 : ℝ)*X 1 0+(-496963507/1000000000 : ℝ)*X 1 1+(163986653/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((15864657/200000000 : ℝ)*X 2 0+(3277966809/5000000000 : ℝ)*X 2 1+(-4974254439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((52512933/1250000000 : ℝ)*X 0 0+(2934625521/5000000000 : ℝ)*X 0 1+(1174627397/2000000000 : ℝ)*X 0 2+(52512933/1250000000 : ℝ)*X 1 0+(2934625521/5000000000 : ℝ)*X 1 1+(1174627397/2000000000 : ℝ)*X 1 2+(52512933/1250000000 : ℝ)*X 2 0+(2934625521/5000000000 : ℝ)*X 2 1+(1174627397/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (770734345471546299327792699/388625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (498299667419309/25000000000000 : ℝ)*(major0) + (498299667419309/25000000000000 : ℝ)*(major1) + (498299667419309/25000000000000 : ℝ)*(major2) + (2640088118385737/100000000000000 : ℝ)*(sp0) + (660024516203549/25000000000000 : ℝ)*(sp1) + (660024814882449/25000000000000 : ℝ)*(sp2) + (673143457028459/50000000000000 : ℝ)*(sp3) + (19701181317/100000000000000 : ℝ)*(sp4) + (9708950147/100000000000000 : ℝ)*(sp5) + (860973963/10000000000000 : ℝ)*(sp6) + (1176262797/100000000000000 : ℝ)*(sp8) + (305516377/25000000000000 : ℝ)*(sp9) + (45062417/4000000000000 : ℝ)*(sp10) + (1363359891/100000000000000 : ℝ)*(sp11) + (1346288277416809/100000000000000 : ℝ)*(f.failure) + (52802179916597/2000000000000 : ℝ)*(f.sum) + (425281525487/242890625000000000000000000 : ℝ)*base65 + (1397484811406128589/777250000000000000000000000000000 : ℝ)*base67 + (2667178801524378589/777250000000000000000000000000000 : ℝ)*base69 + (4178787367855628589/777250000000000000000000000000000 : ℝ)*base71 + (17221504010253/15545000000000000000000000000 : ℝ)*base73 + (4660738900357128589/777250000000000000000000000000000 : ℝ)*base75 + (2846508955131128589/777250000000000000000000000000000 : ℝ)*base77 + (1454330875764628589/777250000000000000000000000000000 : ℝ)*base79 + (10789580299607/3886250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (44591891/5000000000000000000000 : ℝ)*base90 + (44591891/5000000000000000000000 : ℝ)*base92 + (44591891/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99049278536787798643809/7772500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2022704975689007/100000000000000 : ℝ)*(major0) + (2022704975689007/100000000000000 : ℝ)*(major1) + (2022704975689007/100000000000000 : ℝ)*(major2) + (239850517/25000000000000 : ℝ)*(sp1) + (82932767/20000000000000 : ℝ)*(sp2) + (304594981/100000000000000 : ℝ)*(sp3) + (334898748282331/12500000000000 : ℝ)*(sp4) + (669797453827067/25000000000000 : ℝ)*(sp5) + (669797556553621/25000000000000 : ℝ)*(sp6) + (683108379220577/50000000000000 : ℝ)*(sp7) + (1491491273/100000000000000 : ℝ)*(sp8) + (351519793/50000000000000 : ℝ)*(sp9) + (418435801/50000000000000 : ℝ)*(sp10) + (492903399/50000000000000 : ℝ)*(sp11) + (1366218048842933/100000000000000 : ℝ)*(f.failure) + (1339595738874961/50000000000000 : ℝ)*(f.sum) + (18236833105691/15545000000000000000000000000 : ℝ)*base65 + (244240795451189553/3109000000000000000000000000000000 : ℝ)*base68 + (3707676831004810447/3109000000000000000000000000000000 : ℝ)*base69 + (16729162934053189553/3109000000000000000000000000000000 : ℝ)*base72 + (4883747243593/1943125000000000000000000000 : ℝ)*base74 + (1828086214300189553/3109000000000000000000000000000000 : ℝ)*base76 + (7760089157878810447/3109000000000000000000000000000000 : ℝ)*base77 + (9346238479414810447/3109000000000000000000000000000000 : ℝ)*base79 + (7320998214711/3886250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (4221033/5000000000000000000000 : ℝ)*base89 + (4221033/5000000000000000000000 : ℝ)*base91 + (4221033/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1069_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2597/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8727/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1069_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8727/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16731/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1069_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1069_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1069_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8727/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16731/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1069_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
