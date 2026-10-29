-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1520_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:11.957161+00:00
-- url     : https://prove2.me/submissions/3ac82ce3-2493-4e29-8777-dd7fec7588c1

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
theorem support_rectangle_w1520_s3_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1855809913/10000000000 : ℝ)*x 0 + (54351843/100000000 : ℝ)*x 1 + (208613621/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1855809913/10000000000 : ℝ)^4537 ≤ (1135845409549/10000000000000 : ℝ)^3513 := by
    have hnat : (1855809913 : ℕ)^4537*10000000000000^3513 ≤ 1135845409549^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855809913 10000000000 1135845409549 10000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54351843/100000000 : ℝ)^4537 ≤ (45502180977077/100000000000000 : ℝ)^3513 := by
    have hnat : (54351843 : ℕ)^4537*100000000000000^3513 ≤ 45502180977077^3513*100000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54351843 100000000 45502180977077 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208613621/400000000 : ℝ)^4537 ≤ (43139364913259/100000000000000 : ℝ)^3513 := by
    have hnat : (208613621 : ℕ)^4537*100000000000000^3513 ≤ 43139364913259^3513*400000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208613621 400000000 43139364913259 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1855809913/10000000000 : ℝ), (54351843/100000000 : ℝ), (208613621/400000000 : ℝ)] ![(1135845409549/10000000000000 : ℝ), (45502180977077/100000000000000 : ℝ), (43139364913259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1855809913/10000000000 : ℝ)|^4537 ≤ (1135845409549/10000000000000 : ℝ)^3513
        have hw : |(-1855809913/10000000000 : ℝ)|=(1855809913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54351843/100000000 : ℝ)|^4537 ≤ (45502180977077/100000000000000 : ℝ)^3513
        have hw : |(54351843/100000000 : ℝ)|=(54351843/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208613621/400000000 : ℝ)|^4537 ≤ (43139364913259/100000000000000 : ℝ)^3513
        have hw : |(208613621/400000000 : ℝ)|=(208613621/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s3_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070385159/2000000000 : ℝ)*x 0 + (-24605691/125000000 : ℝ)*x 1 + (2607670397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070385159/2000000000 : ℝ)^4537 ≤ (22302000924927/50000000000000 : ℝ)^3513 := by
    have hnat : (1070385159 : ℕ)^4537*50000000000000^3513 ≤ 22302000924927^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070385159 2000000000 22302000924927 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24605691/125000000 : ℝ)^4537 ≤ (6128315173979/50000000000000 : ℝ)^3513 := by
    have hnat : (24605691 : ℕ)^4537*50000000000000^3513 ≤ 6128315173979^3513*125000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24605691 125000000 6128315173979 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607670397/5000000000 : ℝ)^4537 ≤ (43139367786909/100000000000000 : ℝ)^3513 := by
    have hnat : (2607670397 : ℕ)^4537*100000000000000^3513 ≤ 43139367786909^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607670397 5000000000 43139367786909 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070385159/2000000000 : ℝ), (-24605691/125000000 : ℝ), (2607670397/5000000000 : ℝ)] ![(22302000924927/50000000000000 : ℝ), (6128315173979/50000000000000 : ℝ), (43139367786909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070385159/2000000000 : ℝ)|^4537 ≤ (22302000924927/50000000000000 : ℝ)^3513
        have hw : |(1070385159/2000000000 : ℝ)|=(1070385159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24605691/125000000 : ℝ)|^4537 ≤ (6128315173979/50000000000000 : ℝ)^3513
        have hw : |(-24605691/125000000 : ℝ)|=(24605691/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607670397/5000000000 : ℝ)|^4537 ≤ (43139367786909/100000000000000 : ℝ)^3513
        have hw : |(2607670397/5000000000 : ℝ)|=(2607670397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s3_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668990731/1250000000 : ℝ)*x 0 + (1303835179/2500000000 : ℝ)*x 1 + (-1968455313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668990731/1250000000 : ℝ)^4537 ≤ (278775015127/625000000000 : ℝ)^3513 := by
    have hnat : (668990731 : ℕ)^4537*625000000000^3513 ≤ 278775015127^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668990731 1250000000 278775015127 625000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303835179/2500000000 : ℝ)^4537 ≤ (21569683476829/50000000000000 : ℝ)^3513 := by
    have hnat : (1303835179 : ℕ)^4537*50000000000000^3513 ≤ 21569683476829^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303835179 2500000000 21569683476829 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1968455313/10000000000 : ℝ)^4537 ≤ (12256630613327/100000000000000 : ℝ)^3513 := by
    have hnat : (1968455313 : ℕ)^4537*100000000000000^3513 ≤ 12256630613327^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968455313 10000000000 12256630613327 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668990731/1250000000 : ℝ), (1303835179/2500000000 : ℝ), (-1968455313/10000000000 : ℝ)] ![(278775015127/625000000000 : ℝ), (21569683476829/50000000000000 : ℝ), (12256630613327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668990731/1250000000 : ℝ)|^4537 ≤ (278775015127/625000000000 : ℝ)^3513
        have hw : |(668990731/1250000000 : ℝ)|=(668990731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303835179/2500000000 : ℝ)|^4537 ≤ (21569683476829/50000000000000 : ℝ)^3513
        have hw : |(1303835179/2500000000 : ℝ)|=(1303835179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1968455313/10000000000 : ℝ)|^4537 ≤ (12256630613327/100000000000000 : ℝ)^3513
        have hw : |(-1968455313/10000000000 : ℝ)|=(1968455313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s3_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066444329/2500000000 : ℝ)*x 0 + (1005331169/2500000000 : ℝ)*x 1 + (113066273/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066444329/2500000000 : ℝ)^4537 ≤ (16638601282661/50000000000000 : ℝ)^3513 := by
    have hnat : (1066444329 : ℕ)^4537*50000000000000^3513 ≤ 16638601282661^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066444329 2500000000 16638601282661 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005331169/2500000000 : ℝ)^4537 ≤ (15417614967351/50000000000000 : ℝ)^3513 := by
    have hnat : (1005331169 : ℕ)^4537*50000000000000^3513 ≤ 15417614967351^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005331169 2500000000 15417614967351 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113066273/250000000 : ℝ)^4537 ≤ (4485945935777/12500000000000 : ℝ)^3513 := by
    have hnat : (113066273 : ℕ)^4537*12500000000000^3513 ≤ 4485945935777^3513*250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113066273 250000000 4485945935777 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066444329/2500000000 : ℝ), (1005331169/2500000000 : ℝ), (113066273/250000000 : ℝ)] ![(16638601282661/50000000000000 : ℝ), (15417614967351/50000000000000 : ℝ), (4485945935777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066444329/2500000000 : ℝ)|^4537 ≤ (16638601282661/50000000000000 : ℝ)^3513
        have hw : |(1066444329/2500000000 : ℝ)|=(1066444329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005331169/2500000000 : ℝ)|^4537 ≤ (15417614967351/50000000000000 : ℝ)^3513
        have hw : |(1005331169/2500000000 : ℝ)|=(1005331169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113066273/250000000 : ℝ)|^4537 ≤ (4485945935777/12500000000000 : ℝ)^3513
        have hw : |(113066273/250000000 : ℝ)|=(113066273/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s3_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-231980091/1250000000 : ℝ)*x 0 + (5216504013/10000000000 : ℝ)*x 1 + (169812879/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231980091/1250000000 : ℝ)^4537 ≤ (11358697674347/100000000000000 : ℝ)^3513 := by
    have hnat : (231980091 : ℕ)^4537*100000000000000^3513 ≤ 11358697674347^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231980091 1250000000 11358697674347 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216504013/10000000000 : ℝ)^4537 ≤ (43151794529917/100000000000000 : ℝ)^3513 := by
    have hnat : (5216504013 : ℕ)^4537*100000000000000^3513 ≤ 43151794529917^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216504013 10000000000 43151794529917 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169812879/312500000 : ℝ)^4537 ≤ (45489507777931/100000000000000 : ℝ)^3513 := by
    have hnat : (169812879 : ℕ)^4537*100000000000000^3513 ≤ 45489507777931^3513*312500000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169812879 312500000 45489507777931 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231980091/1250000000 : ℝ), (5216504013/10000000000 : ℝ), (169812879/312500000 : ℝ)] ![(11358697674347/100000000000000 : ℝ), (43151794529917/100000000000000 : ℝ), (45489507777931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231980091/1250000000 : ℝ)|^4537 ≤ (11358697674347/100000000000000 : ℝ)^3513
        have hw : |(-231980091/1250000000 : ℝ)|=(231980091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216504013/10000000000 : ℝ)|^4537 ≤ (43151794529917/100000000000000 : ℝ)^3513
        have hw : |(5216504013/10000000000 : ℝ)|=(5216504013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169812879/312500000 : ℝ)|^4537 ≤ (45489507777931/100000000000000 : ℝ)^3513
        have hw : |(169812879/312500000 : ℝ)|=(169812879/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s3_5 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647072411/5000000000 : ℝ)*x 0 + (-874891561/5000000000 : ℝ)*x 1 + (5434012067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647072411/5000000000 : ℝ)^4537 ≤ (21991528114473/50000000000000 : ℝ)^3513 := by
    have hnat : (2647072411 : ℕ)^4537*50000000000000^3513 ≤ 21991528114473^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647072411 5000000000 21991528114473 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874891561/5000000000 : ℝ)^4537 ≤ (10527436633309/100000000000000 : ℝ)^3513 := by
    have hnat : (874891561 : ℕ)^4537*100000000000000^3513 ≤ 10527436633309^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874891561 5000000000 10527436633309 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434012067/10000000000 : ℝ)^4537 ≤ (45489507118437/100000000000000 : ℝ)^3513 := by
    have hnat : (5434012067 : ℕ)^4537*100000000000000^3513 ≤ 45489507118437^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434012067 10000000000 45489507118437 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647072411/5000000000 : ℝ), (-874891561/5000000000 : ℝ), (5434012067/10000000000 : ℝ)] ![(21991528114473/50000000000000 : ℝ), (10527436633309/100000000000000 : ℝ), (45489507118437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647072411/5000000000 : ℝ)|^4537 ≤ (21991528114473/50000000000000 : ℝ)^3513
        have hw : |(2647072411/5000000000 : ℝ)|=(2647072411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-874891561/5000000000 : ℝ)|^4537 ≤ (10527436633309/100000000000000 : ℝ)^3513
        have hw : |(-874891561/5000000000 : ℝ)|=(874891561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434012067/10000000000 : ℝ)|^4537 ≤ (45489507118437/100000000000000 : ℝ)^3513
        have hw : |(5434012067/10000000000 : ℝ)|=(5434012067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s3_6 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529414471/1000000000 : ℝ)*x 0 + (1086802401/2000000000 : ℝ)*x 1 + (-437445841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529414471/1000000000 : ℝ)^4537 ≤ (1099576375681/2500000000000 : ℝ)^3513 := by
    have hnat : (529414471 : ℕ)^4537*2500000000000^3513 ≤ 1099576375681^3513*1000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529414471 1000000000 1099576375681 2500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086802401/2000000000 : ℝ)^4537 ≤ (45489506448131/100000000000000 : ℝ)^3513 := by
    have hnat : (1086802401 : ℕ)^4537*100000000000000^3513 ≤ 45489506448131^3513*2000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086802401 2000000000 45489506448131 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437445841/2500000000 : ℝ)^4537 ≤ (10527438513683/100000000000000 : ℝ)^3513 := by
    have hnat : (437445841 : ℕ)^4537*100000000000000^3513 ≤ 10527438513683^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437445841 2500000000 10527438513683 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529414471/1000000000 : ℝ), (1086802401/2000000000 : ℝ), (-437445841/2500000000 : ℝ)] ![(1099576375681/2500000000000 : ℝ), (45489506448131/100000000000000 : ℝ), (10527438513683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529414471/1000000000 : ℝ)|^4537 ≤ (1099576375681/2500000000000 : ℝ)^3513
        have hw : |(529414471/1000000000 : ℝ)|=(529414471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086802401/2000000000 : ℝ)|^4537 ≤ (45489506448131/100000000000000 : ℝ)^3513
        have hw : |(1086802401/2000000000 : ℝ)|=(1086802401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437445841/2500000000 : ℝ)|^4537 ≤ (10527438513683/100000000000000 : ℝ)^3513
        have hw : |(-437445841/2500000000 : ℝ)|=(437445841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s3_7 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4265848309/10000000000 : ℝ)*x 0 + (4519997851/10000000000 : ℝ)*x 1 + (4023997457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265848309/10000000000 : ℝ)^4537 ≤ (33277917811987/100000000000000 : ℝ)^3513 := by
    have hnat : (4265848309 : ℕ)^4537*100000000000000^3513 ≤ 33277917811987^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265848309 10000000000 33277917811987 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519997851/10000000000 : ℝ)^4537 ≤ (17930190502767/50000000000000 : ℝ)^3513 := by
    have hnat : (4519997851 : ℕ)^4537*50000000000000^3513 ≤ 17930190502767^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519997851 10000000000 17930190502767 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023997457/10000000000 : ℝ)^4537 ≤ (15430850582257/50000000000000 : ℝ)^3513 := by
    have hnat : (4023997457 : ℕ)^4537*50000000000000^3513 ≤ 15430850582257^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023997457 10000000000 15430850582257 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265848309/10000000000 : ℝ), (4519997851/10000000000 : ℝ), (4023997457/10000000000 : ℝ)] ![(33277917811987/100000000000000 : ℝ), (17930190502767/50000000000000 : ℝ), (15430850582257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265848309/10000000000 : ℝ)|^4537 ≤ (33277917811987/100000000000000 : ℝ)^3513
        have hw : |(4265848309/10000000000 : ℝ)|=(4265848309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519997851/10000000000 : ℝ)|^4537 ≤ (17930190502767/50000000000000 : ℝ)^3513
        have hw : |(4519997851/10000000000 : ℝ)|=(4519997851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023997457/10000000000 : ℝ)|^4537 ≤ (15430850582257/50000000000000 : ℝ)^3513
        have hw : |(4023997457/10000000000 : ℝ)|=(4023997457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15967/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10889/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3109/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15967/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15967/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15967/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15967/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15967/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15967/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10501/100000 : ℝ) ^ (4535/1024 : ℝ) ≤ (1156787322895891/25000000000000000000 : ℝ) := by
    have hpowers : (10501/100000 : ℝ)^4535 ≤ (1156787322895891/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10501 : ℕ)^4535*25000000000000000000^1024 ≤ 1156787322895891^1024*100000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10501 100000 1156787322895891 25000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10501/100000 : ℝ)) (X := (1156787322895891/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15967/100000 : ℝ) ^ (4535/1024 : ℝ) ≤ (14800501467083721/50000000000000000000 : ℝ) := by
    have hpowers : (15967/100000 : ℝ)^4535 ≤ (14800501467083721/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15967 : ℕ)^4535*50000000000000000000^1024 ≤ 14800501467083721^1024*100000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15967 100000 14800501467083721 50000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15967/100000 : ℝ)) (X := (14800501467083721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501156787322895891/12500000000000000000 : ℝ) ≤ (312506529811391/312500000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (12501156787322895891/12500000000000000000 : ℝ)^1024 ≤ (312506529811391/312500000000000 : ℝ)^4535 := by
      have hnat : (12501156787322895891 : ℕ)^1024*312500000000000^4535 ≤ 312506529811391^4535*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501156787322895891 12500000000000000000 312506529811391 312500000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312506529811391/312500000000000 : ℝ)) (X := (12501156787322895891/12500000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017114076112875503/50000000000000000000 : ℝ) ≤ (10000772767030613/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (50017114076112875503/50000000000000000000 : ℝ)^1024 ≤ (10000772767030613/10000000000000000 : ℝ)^4535 := by
      have hnat : (50017114076112875503 : ℕ)^1024*10000000000000000^4535 ≤ 10000772767030613^4535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017114076112875503 50000000000000000000 10000772767030613 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000772767030613/10000000000000000 : ℝ)) (X := (50017114076112875503/50000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014800501467083721/25000000000000000000 : ℝ) ≤ (5000668290048357/5000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (25014800501467083721/25000000000000000000 : ℝ)^1024 ≤ (5000668290048357/5000000000000000 : ℝ)^4535 := by
      have hnat : (25014800501467083721 : ℕ)^1024*5000000000000000^4535 ≤ 5000668290048357^4535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014800501467083721 25000000000000000000 5000668290048357 5000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000668290048357/5000000000000000 : ℝ)) (X := (25014800501467083721/25000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1156787322895891/25000000000000000000 : ℝ) ≤ ((5464930094035576939/5466000000000000000 : ℝ)+2*(563813066101/546600000000000 : ℝ)*(10501/100000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (5464930094035576939/5466000000000000000 : ℝ)+2*(563813066101/546600000000000 : ℝ)*(10501/100000 : ℝ)=(312506529811391/312500000000000 : ℝ) by norm_num, show 1+2*(1156787322895891/25000000000000000000 : ℝ)=(12501156787322895891/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14800501467083721/50000000000000000000 : ℝ)+(1156787322895891/25000000000000000000 : ℝ) ≤ ((5464930094035576939/5466000000000000000 : ℝ)+(563813066101/546600000000000 : ℝ)*((15967/100000 : ℝ)+(10501/100000 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (5464930094035576939/5466000000000000000 : ℝ)+(563813066101/546600000000000 : ℝ)*((15967/100000 : ℝ)+(10501/100000 : ℝ))=(10000772767030613/10000000000000000 : ℝ) by norm_num, show 1+(14800501467083721/50000000000000000000 : ℝ)+(1156787322895891/25000000000000000000 : ℝ)=(50017114076112875503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14800501467083721/50000000000000000000 : ℝ) ≤ ((5464930094035576939/5466000000000000000 : ℝ)+2*(563813066101/546600000000000 : ℝ)*(15967/100000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (5464930094035576939/5466000000000000000 : ℝ)+2*(563813066101/546600000000000 : ℝ)*(15967/100000 : ℝ)=(5000668290048357/5000000000000000 : ℝ) by norm_num, show 1+2*(14800501467083721/50000000000000000000 : ℝ)=(25014800501467083721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5464930094035576939/5466000000000000000 : ℝ)*(X 1 0+X 2 0)+(563813066101/546600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10501/100000 : ℝ)) (hi := (15967/100000 : ℝ)) (c := (5464930094035576939/5466000000000000000 : ℝ)) (alpha := (563813066101/546600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5464930094035576939/5466000000000000000 : ℝ)*(X 0 1+X 2 1)+(563813066101/546600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10501/100000 : ℝ)) (hi := (15967/100000 : ℝ)) (c := (5464930094035576939/5466000000000000000 : ℝ)) (alpha := (563813066101/546600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5464930094035576939/5466000000000000000 : ℝ)*(X 0 2+X 1 2)+(563813066101/546600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10501/100000 : ℝ)) (hi := (15967/100000 : ℝ)) (c := (5464930094035576939/5466000000000000000 : ℝ)) (alpha := (563813066101/546600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1855809913/10000000000 : ℝ)*X 0 0+(54351843/100000000 : ℝ)*X 0 1+(208613621/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070385159/2000000000 : ℝ)*X 1 0+(-24605691/125000000 : ℝ)*X 1 1+(2607670397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668990731/1250000000 : ℝ)*X 2 0+(1303835179/2500000000 : ℝ)*X 2 1+(-1968455313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1066444329/2500000000 : ℝ)*X 0 0+(1005331169/2500000000 : ℝ)*X 0 1+(113066273/250000000 : ℝ)*X 0 2+(1066444329/2500000000 : ℝ)*X 1 0+(1005331169/2500000000 : ℝ)*X 1 1+(113066273/250000000 : ℝ)*X 1 2+(1066444329/2500000000 : ℝ)*X 2 0+(1005331169/2500000000 : ℝ)*X 2 1+(113066273/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-231980091/1250000000 : ℝ)*X 0 0+(5216504013/10000000000 : ℝ)*X 0 1+(169812879/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647072411/5000000000 : ℝ)*X 1 0+(-874891561/5000000000 : ℝ)*X 1 1+(5434012067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529414471/1000000000 : ℝ)*X 2 0+(1086802401/2000000000 : ℝ)*X 2 1+(-437445841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4265848309/10000000000 : ℝ)*X 0 0+(4519997851/10000000000 : ℝ)*X 0 1+(4023997457/10000000000 : ℝ)*X 0 2+(4265848309/10000000000 : ℝ)*X 1 0+(4519997851/10000000000 : ℝ)*X 1 1+(4023997457/10000000000 : ℝ)*X 1 2+(4265848309/10000000000 : ℝ)*X 2 0+(4519997851/10000000000 : ℝ)*X 2 1+(4023997457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53434215833502465227891453/9110000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (850445539/100000000000000 : ℝ)*(base19) + (833002783/100000000000000 : ℝ)*(base23) + (33443421/100000000000000 : ℝ)*(lower2) + (3995057/2000000000000 : ℝ)*(upper3) + (64915079/50000000000000 : ℝ)*(upper5) + (327171985457309/10000000000000 : ℝ)*(major0) + (327171985457309/10000000000000 : ℝ)*(major1) + (327171985457309/10000000000000 : ℝ)*(major2) + (90974014488697/2000000000000 : ℝ)*(sp0) + (35536835492309/781250000000 : ℝ)*(sp1) + (4548714960458307/100000000000000 : ℝ)*(sp2) + (1994715833852539/100000000000000 : ℝ)*(sp3) + (47090707/312500000000 : ℝ)*(sp4) + (7886317663/100000000000000 : ℝ)*(sp7) + (1994723720170201/100000000000000 : ℝ)*(f.failure) + (4548715793461091/100000000000000 : ℝ)*(f.sum) + (128352748381/42703125000000000000000000 : ℝ)*base66 + (268331685706532849/54660000000000000000000000000000 : ℝ)*base68 + (239703682557572849/54660000000000000000000000000000 : ℝ)*base70 + (453847743962972849/54660000000000000000000000000000 : ℝ)*base72 + (1081764301063/683250000000000000000000000 : ℝ)*base74 + (648806087319452849/54660000000000000000000000000000 : ℝ)*base76 + (1182173413374332849/54660000000000000000000000000000 : ℝ)*base78 + (949524922391252849/54660000000000000000000000000000 : ℝ)*base80 + (5246768161469/2733000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (13751903/10000000000000000000000 : ℝ)*base90 + (13751903/10000000000000000000000 : ℝ)*base92 + (13751903/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1461347388803613002221779/711718750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1331981399/100000000000000 : ℝ)*(base19) + (1540182319/100000000000000 : ℝ)*(base23) + (129977213/100000000000000 : ℝ)*(upper3) + (38910767/25000000000000 : ℝ)*(lower4) + (4598291/10000000000000 : ℝ)*(upper5) + (206676592798131/6250000000000 : ℝ)*(major0) + (206676592798131/6250000000000 : ℝ)*(major1) + (206676592798131/6250000000000 : ℝ)*(major2) + (20586105567/100000000000000 : ℝ)*(sp1) + (21637213891/100000000000000 : ℝ)*(sp2) + (574690468622277/12500000000000 : ℝ)*(sp4) + (3678001464713/80000000000 : ℝ)*(sp5) + (2298750285791003/50000000000000 : ℝ)*(sp6) + (403225430423959/20000000000000 : ℝ)*(sp7) + (403225430423959/20000000000000 : ℝ)*(f.failure) + (574690468622277/12500000000000 : ℝ)*(f.sum) + (10115887273731/4555000000000000000000000000 : ℝ)*base65 + (52243802234550497/11387500000000000000000000000000 : ℝ)*base68 + (84520942656574503/11387500000000000000000000000000 : ℝ)*base69 + (52428462896237003/11387500000000000000000000000000 : ℝ)*base71 + (19035834315559/4555000000000000000000000000 : ℝ)*base74 + (19856906615324503/11387500000000000000000000000000 : ℝ)*base75 + (30898861810074503/11387500000000000000000000000000 : ℝ)*base77 + (55191712525974503/11387500000000000000000000000000 : ℝ)*base79 + (587447903843/142343750000000000000000000 : ℝ)*base81 + (7238577/2000000000000000000000 : ℝ)*base90 + (7238577/2000000000000000000000 : ℝ)*base92 + (7238577/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1520_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15967/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10889/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3109/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1520_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1520_s4_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1856210597/10000000000 : ℝ)*x 0 + (2716272701/5000000000 : ℝ)*x 1 + (2608857269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1856210597/10000000000 : ℝ)^4537 ≤ (568081070807/5000000000000 : ℝ)^3513 := by
    have hnat : (1856210597 : ℕ)^4537*5000000000000^3513 ≤ 568081070807^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856210597 10000000000 568081070807 5000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716272701/5000000000 : ℝ)^4537 ≤ (45473651064839/100000000000000 : ℝ)^3513 := by
    have hnat : (2716272701 : ℕ)^4537*100000000000000^3513 ≤ 45473651064839^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716272701 5000000000 45473651064839 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608857269/5000000000 : ℝ)^4537 ≤ (10791181875909/25000000000000 : ℝ)^3513 := by
    have hnat : (2608857269 : ℕ)^4537*25000000000000^3513 ≤ 10791181875909^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608857269 5000000000 10791181875909 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1856210597/10000000000 : ℝ), (2716272701/5000000000 : ℝ), (2608857269/5000000000 : ℝ)] ![(568081070807/5000000000000 : ℝ), (45473651064839/100000000000000 : ℝ), (10791181875909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1856210597/10000000000 : ℝ)|^4537 ≤ (568081070807/5000000000000 : ℝ)^3513
        have hw : |(-1856210597/10000000000 : ℝ)|=(1856210597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716272701/5000000000 : ℝ)|^4537 ≤ (45473651064839/100000000000000 : ℝ)^3513
        have hw : |(2716272701/5000000000 : ℝ)|=(2716272701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608857269/5000000000 : ℝ)|^4537 ≤ (10791181875909/25000000000000 : ℝ)^3513
        have hw : |(2608857269/5000000000 : ℝ)|=(2608857269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s4_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668904287/1250000000 : ℝ)*x 0 + (-245778369/1250000000 : ℝ)*x 1 + (163053577/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668904287/1250000000 : ℝ)^4537 ≤ (696821234779/1562500000000 : ℝ)^3513 := by
    have hnat : (668904287 : ℕ)^4537*1562500000000^3513 ≤ 696821234779^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668904287 1250000000 696821234779 1562500000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245778369/1250000000 : ℝ)^4537 ≤ (12238714242709/100000000000000 : ℝ)^3513 := by
    have hnat : (245778369 : ℕ)^4537*100000000000000^3513 ≤ 12238714242709^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245778369 1250000000 12238714242709 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163053577/312500000 : ℝ)^4537 ≤ (4316472671301/10000000000000 : ℝ)^3513 := by
    have hnat : (163053577 : ℕ)^4537*10000000000000^3513 ≤ 4316472671301^3513*312500000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163053577 312500000 4316472671301 10000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668904287/1250000000 : ℝ), (-245778369/1250000000 : ℝ), (163053577/312500000 : ℝ)] ![(696821234779/1562500000000 : ℝ), (12238714242709/100000000000000 : ℝ), (4316472671301/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668904287/1250000000 : ℝ)|^4537 ≤ (696821234779/1562500000000 : ℝ)^3513
        have hw : |(668904287/1250000000 : ℝ)|=(668904287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245778369/1250000000 : ℝ)|^4537 ≤ (12238714242709/100000000000000 : ℝ)^3513
        have hw : |(-245778369/1250000000 : ℝ)|=(245778369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163053577/312500000 : ℝ)|^4537 ≤ (4316472671301/10000000000000 : ℝ)^3513
        have hw : |(163053577/312500000 : ℝ)|=(163053577/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s4_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351234271/10000000000 : ℝ)*x 0 + (1304428627/2500000000 : ℝ)*x 1 + (-1966226927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351234271/10000000000 : ℝ)^4537 ≤ (22298279378389/50000000000000 : ℝ)^3513 := by
    have hnat : (5351234271 : ℕ)^4537*50000000000000^3513 ≤ 22298279378389^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351234271 10000000000 22298279378389 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304428627/2500000000 : ℝ)^4537 ≤ (5395590897889/12500000000000 : ℝ)^3513 := by
    have hnat : (1304428627 : ℕ)^4537*12500000000000^3513 ≤ 5395590897889^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304428627 2500000000 5395590897889 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966226927/10000000000 : ℝ)^4537 ≤ (12238714041739/100000000000000 : ℝ)^3513 := by
    have hnat : (1966226927 : ℕ)^4537*100000000000000^3513 ≤ 12238714041739^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966226927 10000000000 12238714041739 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351234271/10000000000 : ℝ), (1304428627/2500000000 : ℝ), (-1966226927/10000000000 : ℝ)] ![(22298279378389/50000000000000 : ℝ), (5395590897889/12500000000000 : ℝ), (12238714041739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351234271/10000000000 : ℝ)|^4537 ≤ (22298279378389/50000000000000 : ℝ)^3513
        have hw : |(5351234271/10000000000 : ℝ)|=(5351234271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304428627/2500000000 : ℝ)|^4537 ≤ (5395590897889/12500000000000 : ℝ)^3513
        have hw : |(1304428627/2500000000 : ℝ)|=(1304428627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966226927/10000000000 : ℝ)|^4537 ≤ (12238714041739/100000000000000 : ℝ)^3513
        have hw : |(-1966226927/10000000000 : ℝ)|=(1966226927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s4_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133014071/5000000000 : ℝ)*x 0 + (4027011653/10000000000 : ℝ)*x 1 + (2258453309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133014071/5000000000 : ℝ)^4537 ≤ (6655945925041/20000000000000 : ℝ)^3513 := by
    have hnat : (2133014071 : ℕ)^4537*20000000000000^3513 ≤ 6655945925041^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133014071 5000000000 6655945925041 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4027011653/10000000000 : ℝ)^4537 ≤ (7722889979683/25000000000000 : ℝ)^3513 := by
    have hnat : (4027011653 : ℕ)^4537*25000000000000^3513 ≤ 7722889979683^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027011653 10000000000 7722889979683 25000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258453309/5000000000 : ℝ)^4537 ≤ (7165742089083/20000000000000 : ℝ)^3513 := by
    have hnat : (2258453309 : ℕ)^4537*20000000000000^3513 ≤ 7165742089083^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258453309 5000000000 7165742089083 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133014071/5000000000 : ℝ), (4027011653/10000000000 : ℝ), (2258453309/5000000000 : ℝ)] ![(6655945925041/20000000000000 : ℝ), (7722889979683/25000000000000 : ℝ), (7165742089083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133014071/5000000000 : ℝ)|^4537 ≤ (6655945925041/20000000000000 : ℝ)^3513
        have hw : |(2133014071/5000000000 : ℝ)|=(2133014071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4027011653/10000000000 : ℝ)|^4537 ≤ (7722889979683/25000000000000 : ℝ)^3513
        have hw : |(4027011653/10000000000 : ℝ)|=(4027011653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258453309/5000000000 : ℝ)|^4537 ≤ (7165742089083/20000000000000 : ℝ)^3513
        have hw : |(2258453309/5000000000 : ℝ)|=(2258453309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s4_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-928119739/5000000000 : ℝ)*x 0 + (5218825509/10000000000 : ℝ)*x 1 + (2715713117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928119739/5000000000 : ℝ)^4537 ≤ (35505780381/312500000000 : ℝ)^3513 := by
    have hnat : (928119739 : ℕ)^4537*312500000000^3513 ≤ 35505780381^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928119739 5000000000 35505780381 312500000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218825509/10000000000 : ℝ)^4537 ≤ (4317659763477/10000000000000 : ℝ)^3513 := by
    have hnat : (5218825509 : ℕ)^4537*10000000000000^3513 ≤ 4317659763477^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218825509 10000000000 4317659763477 10000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715713117/5000000000 : ℝ)^4537 ≤ (45461552626001/100000000000000 : ℝ)^3513 := by
    have hnat : (2715713117 : ℕ)^4537*100000000000000^3513 ≤ 45461552626001^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715713117 5000000000 45461552626001 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928119739/5000000000 : ℝ), (5218825509/10000000000 : ℝ), (2715713117/5000000000 : ℝ)] ![(35505780381/312500000000 : ℝ), (4317659763477/10000000000000 : ℝ), (45461552626001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928119739/5000000000 : ℝ)|^4537 ≤ (35505780381/312500000000 : ℝ)^3513
        have hw : |(-928119739/5000000000 : ℝ)|=(928119739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218825509/10000000000 : ℝ)|^4537 ≤ (4317659763477/10000000000000 : ℝ)^3513
        have hw : |(5218825509/10000000000 : ℝ)|=(5218825509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715713117/5000000000 : ℝ)|^4537 ≤ (45461552626001/100000000000000 : ℝ)^3513
        have hw : |(2715713117/5000000000 : ℝ)|=(2715713117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s4_5 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264738559/500000000 : ℝ)*x 0 + (-438128813/2500000000 : ℝ)*x 1 + (2715713117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264738559/500000000 : ℝ)^4537 ≤ (43989776864311/100000000000000 : ℝ)^3513 := by
    have hnat : (264738559 : ℕ)^4537*100000000000000^3513 ≤ 43989776864311^3513*500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264738559 500000000 43989776864311 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438128813/2500000000 : ℝ)^4537 ≤ (2109734100971/20000000000000 : ℝ)^3513 := by
    have hnat : (438128813 : ℕ)^4537*20000000000000^3513 ≤ 2109734100971^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438128813 2500000000 2109734100971 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715713117/5000000000 : ℝ)^4537 ≤ (45461552626001/100000000000000 : ℝ)^3513 := by
    have hnat : (2715713117 : ℕ)^4537*100000000000000^3513 ≤ 45461552626001^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715713117 5000000000 45461552626001 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264738559/500000000 : ℝ), (-438128813/2500000000 : ℝ), (2715713117/5000000000 : ℝ)] ![(43989776864311/100000000000000 : ℝ), (2109734100971/20000000000000 : ℝ), (45461552626001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264738559/500000000 : ℝ)|^4537 ≤ (43989776864311/100000000000000 : ℝ)^3513
        have hw : |(264738559/500000000 : ℝ)|=(264738559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438128813/2500000000 : ℝ)|^4537 ≤ (2109734100971/20000000000000 : ℝ)^3513
        have hw : |(-438128813/2500000000 : ℝ)|=(438128813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715713117/5000000000 : ℝ)|^4537 ≤ (45461552626001/100000000000000 : ℝ)^3513
        have hw : |(2715713117/5000000000 : ℝ)|=(2715713117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s4_6 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647385597/5000000000 : ℝ)*x 0 + (2715713113/5000000000 : ℝ)*x 1 + (-876257621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647385597/5000000000 : ℝ)^4537 ≤ (43989777014529/100000000000000 : ℝ)^3513 := by
    have hnat : (2647385597 : ℕ)^4537*100000000000000^3513 ≤ 43989777014529^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647385597 5000000000 43989777014529 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715713113/5000000000 : ℝ)^4537 ≤ (45461552539521/100000000000000 : ℝ)^3513 := by
    have hnat : (2715713113 : ℕ)^4537*100000000000000^3513 ≤ 45461552539521^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715713113 5000000000 45461552539521 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876257621/5000000000 : ℝ)^4537 ≤ (10548670427119/100000000000000 : ℝ)^3513 := by
    have hnat : (876257621 : ℕ)^4537*100000000000000^3513 ≤ 10548670427119^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876257621 5000000000 10548670427119 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647385597/5000000000 : ℝ), (2715713113/5000000000 : ℝ), (-876257621/5000000000 : ℝ)] ![(43989777014529/100000000000000 : ℝ), (45461552539521/100000000000000 : ℝ), (10548670427119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647385597/5000000000 : ℝ)|^4537 ≤ (43989777014529/100000000000000 : ℝ)^3513
        have hw : |(2647385597/5000000000 : ℝ)|=(2647385597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715713113/5000000000 : ℝ)|^4537 ≤ (45461552539521/100000000000000 : ℝ)^3513
        have hw : |(2715713113/5000000000 : ℝ)|=(2715713113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-876257621/5000000000 : ℝ)|^4537 ≤ (10548670427119/100000000000000 : ℝ)^3513
        have hw : |(-876257621/5000000000 : ℝ)|=(876257621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s4_7 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533261753/1250000000 : ℝ)*x 0 + (4514373077/10000000000 : ℝ)*x 1 + (4029563961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533261753/1250000000 : ℝ)^4537 ≤ (1040012293449/3125000000000 : ℝ)^3513 := by
    have hnat : (533261753 : ℕ)^4537*3125000000000^3513 ≤ 1040012293449^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533261753 1250000000 1040012293449 3125000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514373077/10000000000 : ℝ)^4537 ≤ (35802758308577/100000000000000 : ℝ)^3513 := by
    have hnat : (4514373077 : ℕ)^4537*100000000000000^3513 ≤ 35802758308577^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514373077 10000000000 35802758308577 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029563961/10000000000 : ℝ)^4537 ≤ (30916848285001/100000000000000 : ℝ)^3513 := by
    have hnat : (4029563961 : ℕ)^4537*100000000000000^3513 ≤ 30916848285001^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029563961 10000000000 30916848285001 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533261753/1250000000 : ℝ), (4514373077/10000000000 : ℝ), (4029563961/10000000000 : ℝ)] ![(1040012293449/3125000000000 : ℝ), (35802758308577/100000000000000 : ℝ), (30916848285001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533261753/1250000000 : ℝ)|^4537 ≤ (1040012293449/3125000000000 : ℝ)^3513
        have hw : |(533261753/1250000000 : ℝ)|=(533261753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514373077/10000000000 : ℝ)|^4537 ≤ (35802758308577/100000000000000 : ℝ)^3513
        have hw : |(4514373077/10000000000 : ℝ)|=(4514373077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029563961/10000000000 : ℝ)|^4537 ≤ (30916848285001/100000000000000 : ℝ)^3513
        have hw : |(4029563961/10000000000 : ℝ)|=(4029563961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3109/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (547/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3109/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3109/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3109/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3109/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3109/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3109/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10889/100000 : ℝ) ^ (4535/1024 : ℝ) ≤ (2716865990014649/50000000000000000000 : ℝ) := by
    have hpowers : (10889/100000 : ℝ)^4535 ≤ (2716865990014649/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10889 : ℕ)^4535*50000000000000000000^1024 ≤ 2716865990014649^1024*100000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10889 100000 2716865990014649 50000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10889/100000 : ℝ)) (X := (2716865990014649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3109/20000 : ℝ) ^ (4535/1024 : ℝ) ≤ (5257980893176597/20000000000000000000 : ℝ) := by
    have hpowers : (3109/20000 : ℝ)^4535 ≤ (5257980893176597/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3109 : ℕ)^4535*20000000000000000000^1024 ≤ 5257980893176597^1024*20000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3109 20000 5257980893176597 20000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3109/20000 : ℝ)) (X := (5257980893176597/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002716865990014649/25000000000000000000 : ℝ) ≤ (5000122688147527/5000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (25002716865990014649/25000000000000000000 : ℝ)^1024 ≤ (5000122688147527/5000000000000000 : ℝ)^4535 := by
      have hnat : (25002716865990014649 : ℕ)^1024*5000000000000000^4535 ≤ 5000122688147527^4535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002716865990014649 25000000000000000000 5000122688147527 5000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000122688147527/5000000000000000 : ℝ)) (X := (25002716865990014649/25000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031723636445912283/100000000000000000000 : ℝ) ≤ (10000716229663411/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (100031723636445912283/100000000000000000000 : ℝ)^1024 ≤ (10000716229663411/10000000000000000 : ℝ)^4535 := by
      have hnat : (100031723636445912283 : ℕ)^1024*10000000000000000^4535 ≤ 10000716229663411^4535*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031723636445912283 100000000000000000000 10000716229663411 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000716229663411/10000000000000000 : ℝ)) (X := (100031723636445912283/100000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005257980893176597/10000000000000000000 : ℝ) ≤ (1250148385378971/1250000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (10005257980893176597/10000000000000000000 : ℝ)^1024 ≤ (1250148385378971/1250000000000000 : ℝ)^4535 := by
      have hnat : (10005257980893176597 : ℕ)^1024*1250000000000000^4535 ≤ 1250148385378971^4535*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005257980893176597 10000000000000000000 1250148385378971 1250000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250148385378971/1250000000000000 : ℝ)) (X := (10005257980893176597/10000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2716865990014649/50000000000000000000 : ℝ) ≤ ((23275444113686846339/23280000000000000000 : ℝ)+2*(470853368357/465600000000000 : ℝ)*(10889/100000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (23275444113686846339/23280000000000000000 : ℝ)+2*(470853368357/465600000000000 : ℝ)*(10889/100000 : ℝ)=(5000122688147527/5000000000000000 : ℝ) by norm_num, show 1+2*(2716865990014649/50000000000000000000 : ℝ)=(25002716865990014649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5257980893176597/20000000000000000000 : ℝ)+(2716865990014649/50000000000000000000 : ℝ) ≤ ((23275444113686846339/23280000000000000000 : ℝ)+(470853368357/465600000000000 : ℝ)*((3109/20000 : ℝ)+(10889/100000 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (23275444113686846339/23280000000000000000 : ℝ)+(470853368357/465600000000000 : ℝ)*((3109/20000 : ℝ)+(10889/100000 : ℝ))=(10000716229663411/10000000000000000 : ℝ) by norm_num, show 1+(5257980893176597/20000000000000000000 : ℝ)+(2716865990014649/50000000000000000000 : ℝ)=(100031723636445912283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5257980893176597/20000000000000000000 : ℝ) ≤ ((23275444113686846339/23280000000000000000 : ℝ)+2*(470853368357/465600000000000 : ℝ)*(3109/20000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (23275444113686846339/23280000000000000000 : ℝ)+2*(470853368357/465600000000000 : ℝ)*(3109/20000 : ℝ)=(1250148385378971/1250000000000000 : ℝ) by norm_num, show 1+2*(5257980893176597/20000000000000000000 : ℝ)=(10005257980893176597/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23275444113686846339/23280000000000000000 : ℝ)*(X 1 0+X 2 0)+(470853368357/465600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10889/100000 : ℝ)) (hi := (3109/20000 : ℝ)) (c := (23275444113686846339/23280000000000000000 : ℝ)) (alpha := (470853368357/465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23275444113686846339/23280000000000000000 : ℝ)*(X 0 1+X 2 1)+(470853368357/465600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10889/100000 : ℝ)) (hi := (3109/20000 : ℝ)) (c := (23275444113686846339/23280000000000000000 : ℝ)) (alpha := (470853368357/465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23275444113686846339/23280000000000000000 : ℝ)*(X 0 2+X 1 2)+(470853368357/465600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (10889/100000 : ℝ)) (hi := (3109/20000 : ℝ)) (c := (23275444113686846339/23280000000000000000 : ℝ)) (alpha := (470853368357/465600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1856210597/10000000000 : ℝ)*X 0 0+(2716272701/5000000000 : ℝ)*X 0 1+(2608857269/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668904287/1250000000 : ℝ)*X 1 0+(-245778369/1250000000 : ℝ)*X 1 1+(163053577/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351234271/10000000000 : ℝ)*X 2 0+(1304428627/2500000000 : ℝ)*X 2 1+(-1966226927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2133014071/5000000000 : ℝ)*X 0 0+(4027011653/10000000000 : ℝ)*X 0 1+(2258453309/5000000000 : ℝ)*X 0 2+(2133014071/5000000000 : ℝ)*X 1 0+(4027011653/10000000000 : ℝ)*X 1 1+(2258453309/5000000000 : ℝ)*X 1 2+(2133014071/5000000000 : ℝ)*X 2 0+(4027011653/10000000000 : ℝ)*X 2 1+(2258453309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-928119739/5000000000 : ℝ)*X 0 0+(5218825509/10000000000 : ℝ)*X 0 1+(2715713117/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264738559/500000000 : ℝ)*X 1 0+(-438128813/2500000000 : ℝ)*X 1 1+(2715713117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647385597/5000000000 : ℝ)*X 2 0+(2715713113/5000000000 : ℝ)*X 2 1+(-876257621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533261753/1250000000 : ℝ)*X 0 0+(4514373077/10000000000 : ℝ)*X 0 1+(4029563961/10000000000 : ℝ)*X 0 2+(533261753/1250000000 : ℝ)*X 1 0+(4514373077/10000000000 : ℝ)*X 1 1+(4029563961/10000000000 : ℝ)*X 1 2+(533261753/1250000000 : ℝ)*X 2 0+(4514373077/10000000000 : ℝ)*X 2 1+(4029563961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1425169582941662581326927681/388000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15631349/2000000000000 : ℝ)*(base19) + (715355627/100000000000000 : ℝ)*(base23) + (23794381/100000000000000 : ℝ)*(lower2) + (5805783/6250000000000 : ℝ)*(upper3) + (40541511/50000000000000 : ℝ)*(upper5) + (3348056418547179/100000000000000 : ℝ)*(major0) + (3348056418547179/100000000000000 : ℝ)*(major1) + (3348056418547179/100000000000000 : ℝ)*(major2) + (2327418042103701/50000000000000 : ℝ)*(sp0) + (2327423416785217/50000000000000 : ℝ)*(sp1) + (4654846899782257/100000000000000 : ℝ)*(sp2) + (3266014968727/160000000000 : ℝ)*(sp3) + (5765465241/50000000000000 : ℝ)*(sp4) + (2872032423/50000000000000 : ℝ)*(sp7) + (2041265099519221/100000000000000 : ℝ)*(f.failure) + (1163711903784471/25000000000000 : ℝ)*(f.sum) + (33049618025661/7760000000000000000000000000 : ℝ)*base65 + (33084940929359227/776000000000000000000000000000000 : ℝ)*base67 + (4964999031206640773/776000000000000000000000000000000 : ℝ)*base70 + (2075688896854640773/776000000000000000000000000000000 : ℝ)*base72 + (36135368950061/7760000000000000000000000000 : ℝ)*base73 + (3612339705318640773/776000000000000000000000000000000 : ℝ)*base76 + (1382380361137359227/776000000000000000000000000000000 : ℝ)*base77 + (4524482263534640773/776000000000000000000000000000000 : ℝ)*base80 + (2157815113619/7760000000000000000000000000 : ℝ)*base82 + (54875037/10000000000000000000000 : ℝ)*base89 + (54875037/10000000000000000000000 : ℝ)*base91 + (54875037/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (498957980103908924956966971/97000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (823811533/100000000000000 : ℝ)*(base19) + (920090853/100000000000000 : ℝ)*(base23) + (104514927/100000000000000 : ℝ)*(upper3) + (37546909/100000000000000 : ℝ)*(lower4) + (55744209/50000000000000 : ℝ)*(upper5) + (845789987441763/25000000000000 : ℝ)*(major0) + (845789987441763/25000000000000 : ℝ)*(major1) + (845789987441763/25000000000000 : ℝ)*(major2) + (6360188983/50000000000000 : ℝ)*(sp1) + (13932803063/100000000000000 : ℝ)*(sp2) + (470365247632027/10000000000000 : ℝ)*(sp4) + (4703638932130771/100000000000000 : ℝ)*(sp5) + (2351818811713177/50000000000000 : ℝ)*(sp6) + (412533450350121/20000000000000 : ℝ)*(sp7) + (412533450350121/20000000000000 : ℝ)*(f.failure) + (470365247632027/10000000000000 : ℝ)*(f.sum) + (2697106505397/1940000000000000000000000000 : ℝ)*base65 + (1727705204056064781/194000000000000000000000000000000 : ℝ)*base68 + (2100627634636064781/194000000000000000000000000000000 : ℝ)*base70 + (1672232304930064781/194000000000000000000000000000000 : ℝ)*base72 + (2608865664543/1940000000000000000000000000 : ℝ)*base74 + (1636809225488064781/194000000000000000000000000000000 : ℝ)*base76 + (1388045009332064781/194000000000000000000000000000000 : ℝ)*base78 + (1046247336188064781/194000000000000000000000000000000 : ℝ)*base80 + (7345334294043/1940000000000000000000000000 : ℝ)*base82 + (212337/2000000000000000000000 : ℝ)*base89 + (212337/2000000000000000000000 : ℝ)*base91 + (212337/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1520_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3109/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (547/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1520_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1520_s5_0 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464064509/2500000000 : ℝ)*x 0 + (1358057337/2500000000 : ℝ)*x 1 + (5217999227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464064509/2500000000 : ℝ)^4537 ≤ (2272399284881/20000000000000 : ℝ)^3513 := by
    have hnat : (464064509 : ℕ)^4537*20000000000000^3513 ≤ 2272399284881^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464064509 2500000000 2272399284881 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358057337/2500000000 : ℝ)^4537 ≤ (45470234381747/100000000000000 : ℝ)^3513 := by
    have hnat : (1358057337 : ℕ)^4537*100000000000000^3513 ≤ 45470234381747^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358057337 2500000000 45470234381747 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217999227/10000000000 : ℝ)^4537 ≤ (43167769183189/100000000000000 : ℝ)^3513 := by
    have hnat : (5217999227 : ℕ)^4537*100000000000000^3513 ≤ 43167769183189^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217999227 10000000000 43167769183189 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464064509/2500000000 : ℝ), (1358057337/2500000000 : ℝ), (5217999227/10000000000 : ℝ)] ![(2272399284881/20000000000000 : ℝ), (45470234381747/100000000000000 : ℝ), (43167769183189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464064509/2500000000 : ℝ)|^4537 ≤ (2272399284881/20000000000000 : ℝ)^3513
        have hw : |(-464064509/2500000000 : ℝ)|=(464064509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358057337/2500000000 : ℝ)|^4537 ≤ (45470234381747/100000000000000 : ℝ)^3513
        have hw : |(1358057337/2500000000 : ℝ)|=(1358057337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217999227/10000000000 : ℝ)|^4537 ≤ (43167769183189/100000000000000 : ℝ)^3513
        have hw : |(5217999227/10000000000 : ℝ)|=(5217999227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s5_1 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675575667/5000000000 : ℝ)*x 0 + (-982979753/5000000000 : ℝ)*x 1 + (5217999261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675575667/5000000000 : ℝ)^4537 ≤ (44595666098259/100000000000000 : ℝ)^3513 := by
    have hnat : (2675575667 : ℕ)^4537*100000000000000^3513 ≤ 44595666098259^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675575667 5000000000 44595666098259 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982979753/5000000000 : ℝ)^4537 ≤ (12236564332727/100000000000000 : ℝ)^3513 := by
    have hnat : (982979753 : ℕ)^4537*100000000000000^3513 ≤ 12236564332727^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982979753 5000000000 12236564332727 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217999261/10000000000 : ℝ)^4537 ≤ (5395971193307/12500000000000 : ℝ)^3513 := by
    have hnat : (5217999261 : ℕ)^4537*12500000000000^3513 ≤ 5395971193307^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217999261 10000000000 5395971193307 12500000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675575667/5000000000 : ℝ), (-982979753/5000000000 : ℝ), (5217999261/10000000000 : ℝ)] ![(44595666098259/100000000000000 : ℝ), (12236564332727/100000000000000 : ℝ), (5395971193307/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675575667/5000000000 : ℝ)|^4537 ≤ (44595666098259/100000000000000 : ℝ)^3513
        have hw : |(2675575667/5000000000 : ℝ)|=(2675575667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982979753/5000000000 : ℝ)|^4537 ≤ (12236564332727/100000000000000 : ℝ)^3513
        have hw : |(-982979753/5000000000 : ℝ)|=(982979753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217999261/10000000000 : ℝ)|^4537 ≤ (5395971193307/12500000000000 : ℝ)^3513
        have hw : |(5217999261/10000000000 : ℝ)|=(5217999261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s5_2 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337787837/2500000000 : ℝ)*x 0 + (260899961/500000000 : ℝ)*x 1 + (-982979771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337787837/2500000000 : ℝ)^4537 ≤ (22297833124471/50000000000000 : ℝ)^3513 := by
    have hnat : (1337787837 : ℕ)^4537*50000000000000^3513 ≤ 22297833124471^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337787837 2500000000 22297833124471 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260899961/500000000 : ℝ)^4537 ≤ (43167769108399/100000000000000 : ℝ)^3513 := by
    have hnat : (260899961 : ℕ)^4537*100000000000000^3513 ≤ 43167769108399^3513*500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260899961 500000000 43167769108399 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982979771/5000000000 : ℝ)^4537 ≤ (12236564622113/100000000000000 : ℝ)^3513 := by
    have hnat : (982979771 : ℕ)^4537*100000000000000^3513 ≤ 12236564622113^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982979771 5000000000 12236564622113 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337787837/2500000000 : ℝ), (260899961/500000000 : ℝ), (-982979771/5000000000 : ℝ)] ![(22297833124471/50000000000000 : ℝ), (43167769108399/100000000000000 : ℝ), (12236564622113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337787837/2500000000 : ℝ)|^4537 ≤ (22297833124471/50000000000000 : ℝ)^3513
        have hw : |(1337787837/2500000000 : ℝ)|=(1337787837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260899961/500000000 : ℝ)|^4537 ≤ (43167769108399/100000000000000 : ℝ)^3513
        have hw : |(260899961/500000000 : ℝ)|=(260899961/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-982979771/5000000000 : ℝ)|^4537 ≤ (12236564622113/100000000000000 : ℝ)^3513
        have hw : |(-982979771/5000000000 : ℝ)|=(982979771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s5_3 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266057781/10000000000 : ℝ)*x 0 + (2013846641/5000000000 : ℝ)*x 1 + (7056591/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266057781/10000000000 : ℝ)^4537 ≤ (6656005647913/20000000000000 : ℝ)^3513 := by
    have hnat : (4266057781 : ℕ)^4537*20000000000000^3513 ≤ 6656005647913^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266057781 10000000000 6656005647913 20000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013846641/5000000000 : ℝ)^4537 ≤ (30898313068087/100000000000000 : ℝ)^3513 := by
    have hnat : (2013846641 : ℕ)^4537*100000000000000^3513 ≤ 30898313068087^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013846641 5000000000 30898313068087 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7056591/15625000 : ℝ)^4537 ≤ (559713416831/1562500000000 : ℝ)^3513 := by
    have hnat : (7056591 : ℕ)^4537*1562500000000^3513 ≤ 559713416831^3513*15625000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7056591 15625000 559713416831 1562500000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266057781/10000000000 : ℝ), (2013846641/5000000000 : ℝ), (7056591/15625000 : ℝ)] ![(6656005647913/20000000000000 : ℝ), (30898313068087/100000000000000 : ℝ), (559713416831/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266057781/10000000000 : ℝ)|^4537 ≤ (6656005647913/20000000000000 : ℝ)^3513
        have hw : |(4266057781/10000000000 : ℝ)|=(4266057781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2013846641/5000000000 : ℝ)|^4537 ≤ (30898313068087/100000000000000 : ℝ)^3513
        have hw : |(2013846641/5000000000 : ℝ)|=(2013846641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7056591/15625000 : ℝ)|^4537 ≤ (559713416831/1562500000000 : ℝ)^3513
        have hw : |(7056591/15625000 : ℝ)|=(7056591/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s5_4 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464071693/2500000000 : ℝ)*x 0 + (5219104339/10000000000 : ℝ)*x 1 + (135777901/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464071693/2500000000 : ℝ)^4537 ≤ (5681111792821/50000000000000 : ℝ)^3513 := by
    have hnat : (464071693 : ℕ)^4537*50000000000000^3513 ≤ 5681111792821^3513*2500000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464071693 2500000000 5681111792821 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219104339/10000000000 : ℝ)^4537 ≤ (345436615199/800000000000 : ℝ)^3513 := by
    have hnat : (5219104339 : ℕ)^4537*800000000000^3513 ≤ 345436615199^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219104339 10000000000 345436615199 800000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135777901/250000000 : ℝ)^4537 ≤ (45458199492953/100000000000000 : ℝ)^3513 := by
    have hnat : (135777901 : ℕ)^4537*100000000000000^3513 ≤ 45458199492953^3513*250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135777901 250000000 45458199492953 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464071693/2500000000 : ℝ), (5219104339/10000000000 : ℝ), (135777901/250000000 : ℝ)] ![(5681111792821/50000000000000 : ℝ), (345436615199/800000000000 : ℝ), (45458199492953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464071693/2500000000 : ℝ)|^4537 ≤ (5681111792821/50000000000000 : ℝ)^3513
        have hw : |(-464071693/2500000000 : ℝ)|=(464071693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219104339/10000000000 : ℝ)|^4537 ≤ (345436615199/800000000000 : ℝ)^3513
        have hw : |(5219104339/10000000000 : ℝ)|=(5219104339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135777901/250000000 : ℝ)|^4537 ≤ (45458199492953/100000000000000 : ℝ)^3513
        have hw : |(135777901/250000000 : ℝ)|=(135777901/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s5_5 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294846581/10000000000 : ℝ)*x 0 + (-876420979/5000000000 : ℝ)*x 1 + (5431116437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294846581/10000000000 : ℝ)^4537 ≤ (21995292955141/50000000000000 : ℝ)^3513 := by
    have hnat : (5294846581 : ℕ)^4537*50000000000000^3513 ≤ 21995292955141^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294846581 10000000000 21995292955141 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876420979/5000000000 : ℝ)^4537 ≤ (10551210281117/100000000000000 : ℝ)^3513 := by
    have hnat : (876420979 : ℕ)^4537*100000000000000^3513 ≤ 10551210281117^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876420979 5000000000 10551210281117 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431116437/10000000000 : ℝ)^4537 ≤ (22729101892203/50000000000000 : ℝ)^3513 := by
    have hnat : (5431116437 : ℕ)^4537*50000000000000^3513 ≤ 22729101892203^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431116437 10000000000 22729101892203 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294846581/10000000000 : ℝ), (-876420979/5000000000 : ℝ), (5431116437/10000000000 : ℝ)] ![(21995292955141/50000000000000 : ℝ), (10551210281117/100000000000000 : ℝ), (22729101892203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294846581/10000000000 : ℝ)|^4537 ≤ (21995292955141/50000000000000 : ℝ)^3513
        have hw : |(5294846581/10000000000 : ℝ)|=(5294846581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-876420979/5000000000 : ℝ)|^4537 ≤ (10551210281117/100000000000000 : ℝ)^3513
        have hw : |(-876420979/5000000000 : ℝ)|=(876420979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431116437/10000000000 : ℝ)|^4537 ≤ (22729101892203/50000000000000 : ℝ)^3513
        have hw : |(5431116437/10000000000 : ℝ)|=(5431116437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s5_6 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294846607/10000000000 : ℝ)*x 0 + (5431116481/10000000000 : ℝ)*x 1 + (-1752841863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294846607/10000000000 : ℝ)^4537 ≤ (2199529309463/5000000000000 : ℝ)^3513 := by
    have hnat : (5294846607 : ℕ)^4537*5000000000000^3513 ≤ 2199529309463^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294846607 10000000000 2199529309463 5000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431116481/10000000000 : ℝ)^4537 ≤ (45458204260033/100000000000000 : ℝ)^3513 := by
    have hnat : (5431116481 : ℕ)^4537*100000000000000^3513 ≤ 45458204260033^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431116481 10000000000 45458204260033 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1752841863/10000000000 : ℝ)^4537 ≤ (5275604771289/50000000000000 : ℝ)^3513 := by
    have hnat : (1752841863 : ℕ)^4537*50000000000000^3513 ≤ 5275604771289^3513*10000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752841863 10000000000 5275604771289 50000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294846607/10000000000 : ℝ), (5431116481/10000000000 : ℝ), (-1752841863/10000000000 : ℝ)] ![(2199529309463/5000000000000 : ℝ), (45458204260033/100000000000000 : ℝ), (5275604771289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294846607/10000000000 : ℝ)|^4537 ≤ (2199529309463/5000000000000 : ℝ)^3513
        have hw : |(5294846607/10000000000 : ℝ)|=(5294846607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431116481/10000000000 : ℝ)|^4537 ≤ (45458204260033/100000000000000 : ℝ)^3513
        have hw : |(5431116481/10000000000 : ℝ)|=(5431116481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1752841863/10000000000 : ℝ)|^4537 ≤ (5275604771289/50000000000000 : ℝ)^3513
        have hw : |(-1752841863/10000000000 : ℝ)|=(1752841863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1520_s5_7 (p : ℝ) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533265387/1250000000 : ℝ)*x 0 + (282106153/625000000 : ℝ)*x 1 + (2015115857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533265387/1250000000 : ℝ)^4537 ≤ (2080042893343/6250000000000 : ℝ)^3513 := by
    have hnat : (533265387 : ℕ)^4537*6250000000000^3513 ≤ 2080042893343^3513*1250000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533265387 1250000000 2080042893343 6250000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282106153/625000000 : ℝ)^4537 ≤ (35795848512737/100000000000000 : ℝ)^3513 := by
    have hnat : (282106153 : ℕ)^4537*100000000000000^3513 ≤ 35795848512737^3513*625000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282106153 625000000 35795848512737 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015115857/5000000000 : ℝ)^4537 ≤ (30923465178231/100000000000000 : ℝ)^3513 := by
    have hnat : (2015115857 : ℕ)^4537*100000000000000^3513 ≤ 30923465178231^3513*5000000000^4537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015115857 5000000000 30923465178231 100000000000000 4537 3513 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4537/1024 : ℝ)) 4537 3513 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533265387/1250000000 : ℝ), (282106153/625000000 : ℝ), (2015115857/5000000000 : ℝ)] ![(2080042893343/6250000000000 : ℝ), (35795848512737/100000000000000 : ℝ), (30923465178231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533265387/1250000000 : ℝ)|^4537 ≤ (2080042893343/6250000000000 : ℝ)^3513
        have hw : |(533265387/1250000000 : ℝ)|=(533265387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282106153/625000000 : ℝ)|^4537 ≤ (35795848512737/100000000000000 : ℝ)^3513
        have hw : |(282106153/625000000 : ℝ)|=(282106153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015115857/5000000000 : ℝ)|^4537 ≤ (30923465178231/100000000000000 : ℝ)^3513
        have hw : |(2015115857/5000000000 : ℝ)|=(2015115857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1520_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (547/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5473/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (547/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (547/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (547/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (547/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (547/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (547/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (547/5000 : ℝ) ^ (4535/1024 : ℝ) ≤ (1109469835007861/20000000000000000000 : ℝ) := by
    have hpowers : (547/5000 : ℝ)^4535 ≤ (1109469835007861/20000000000000000000 : ℝ)^1024 := by
      have hnat : (547 : ℕ)^4535*20000000000000000000^1024 ≤ 1109469835007861^1024*5000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        547 5000 1109469835007861 20000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (547/5000 : ℝ)) (X := (1109469835007861/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4535/1024 : ℝ) ≤ (5176090376600561/20000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4535 ≤ (5176090376600561/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4535*20000000000000000000^1024 ≤ 5176090376600561^1024*10000^4535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 5176090376600561 20000000000000000000 4535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (5176090376600561/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001109469835007861/10000000000000000000 : ℝ) ≤ (5000125253398191/5000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (10001109469835007861/10000000000000000000 : ℝ)^1024 ≤ (5000125253398191/5000000000000000 : ℝ)^4535 := by
      have hnat : (10001109469835007861 : ℕ)^1024*5000000000000000^4535 ≤ 5000125253398191^4535*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001109469835007861 10000000000000000000 5000125253398191 5000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000125253398191/5000000000000000 : ℝ)) (X := (10001109469835007861/10000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003142780105804211/10000000000000000000 : ℝ) ≤ (10000709551352441/10000000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (10003142780105804211/10000000000000000000 : ℝ)^1024 ≤ (10000709551352441/10000000000000000 : ℝ)^4535 := by
      have hnat : (10003142780105804211 : ℕ)^1024*10000000000000000^4535 ≤ 10000709551352441^4535*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003142780105804211 10000000000000000000 10000709551352441 10000000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000709551352441/10000000000000000 : ℝ)) (X := (10003142780105804211/10000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005176090376600561/10000000000000000000 : ℝ) ≤ (20002337191817/20000000000000 : ℝ) ^ (4535/1024 : ℝ) := by
    have hpowers : (10005176090376600561/10000000000000000000 : ℝ)^1024 ≤ (20002337191817/20000000000000 : ℝ)^4535 := by
      have hnat : (10005176090376600561 : ℕ)^1024*20000000000000^4535 ≤ 20002337191817^4535*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005176090376600561 10000000000000000000 20002337191817 20000000000000 1024 4535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20002337191817/20000000000000 : ℝ)) (X := (10005176090376600561/10000000000000000000 : ℝ)) (by norm_num) 4535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1109469835007861/20000000000000000000 : ℝ) ≤ ((2274554795551848359/2275000000000000000 : ℝ)+2*(459044556059/455000000000000 : ℝ)*(547/5000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (2274554795551848359/2275000000000000000 : ℝ)+2*(459044556059/455000000000000 : ℝ)*(547/5000 : ℝ)=(5000125253398191/5000000000000000 : ℝ) by norm_num, show 1+2*(1109469835007861/20000000000000000000 : ℝ)=(10001109469835007861/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5176090376600561/20000000000000000000 : ℝ)+(1109469835007861/20000000000000000000 : ℝ) ≤ ((2274554795551848359/2275000000000000000 : ℝ)+(459044556059/455000000000000 : ℝ)*((1549/10000 : ℝ)+(547/5000 : ℝ)))^(4535/1024 : ℝ) := by
    rw [show (2274554795551848359/2275000000000000000 : ℝ)+(459044556059/455000000000000 : ℝ)*((1549/10000 : ℝ)+(547/5000 : ℝ))=(10000709551352441/10000000000000000 : ℝ) by norm_num, show 1+(5176090376600561/20000000000000000000 : ℝ)+(1109469835007861/20000000000000000000 : ℝ)=(10003142780105804211/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5176090376600561/20000000000000000000 : ℝ) ≤ ((2274554795551848359/2275000000000000000 : ℝ)+2*(459044556059/455000000000000 : ℝ)*(1549/10000 : ℝ))^(4535/1024 : ℝ) := by
    rw [show (2274554795551848359/2275000000000000000 : ℝ)+2*(459044556059/455000000000000 : ℝ)*(1549/10000 : ℝ)=(20002337191817/20000000000000 : ℝ) by norm_num, show 1+2*(5176090376600561/20000000000000000000 : ℝ)=(10005176090376600561/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2274554795551848359/2275000000000000000 : ℝ)*(X 1 0+X 2 0)+(459044556059/455000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (547/5000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2274554795551848359/2275000000000000000 : ℝ)) (alpha := (459044556059/455000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2274554795551848359/2275000000000000000 : ℝ)*(X 0 1+X 2 1)+(459044556059/455000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (547/5000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2274554795551848359/2275000000000000000 : ℝ)) (alpha := (459044556059/455000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2274554795551848359/2275000000000000000 : ℝ)*(X 0 2+X 1 2)+(459044556059/455000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4535/1024 : ℝ)) (lo := (547/5000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2274554795551848359/2275000000000000000 : ℝ)) (alpha := (459044556059/455000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-464064509/2500000000 : ℝ)*X 0 0+(1358057337/2500000000 : ℝ)*X 0 1+(5217999227/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675575667/5000000000 : ℝ)*X 1 0+(-982979753/5000000000 : ℝ)*X 1 1+(5217999261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337787837/2500000000 : ℝ)*X 2 0+(260899961/500000000 : ℝ)*X 2 1+(-982979771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4266057781/10000000000 : ℝ)*X 0 0+(2013846641/5000000000 : ℝ)*X 0 1+(7056591/15625000 : ℝ)*X 0 2+(4266057781/10000000000 : ℝ)*X 1 0+(2013846641/5000000000 : ℝ)*X 1 1+(7056591/15625000 : ℝ)*X 1 2+(4266057781/10000000000 : ℝ)*X 2 0+(2013846641/5000000000 : ℝ)*X 2 1+(7056591/15625000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-464071693/2500000000 : ℝ)*X 0 0+(5219104339/10000000000 : ℝ)*X 0 1+(135777901/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294846581/10000000000 : ℝ)*X 1 0+(-876420979/5000000000 : ℝ)*X 1 1+(5431116437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294846607/10000000000 : ℝ)*X 2 0+(5431116481/10000000000 : ℝ)*X 2 1+(-1752841863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533265387/1250000000 : ℝ)*X 0 0+(282106153/625000000 : ℝ)*X 0 1+(2015115857/5000000000 : ℝ)*X 0 2+(533265387/1250000000 : ℝ)*X 1 0+(282106153/625000000 : ℝ)*X 1 1+(2015115857/5000000000 : ℝ)*X 1 2+(533265387/1250000000 : ℝ)*X 2 0+(282106153/625000000 : ℝ)*X 2 1+(2015115857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1520_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57437311143611699813376069/11375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (413130311/50000000000000 : ℝ)*(base19) + (782539577/100000000000000 : ℝ)*(base23) + (29930859/100000000000000 : ℝ)*(lower2) + (142496843/100000000000000 : ℝ)*(upper3) + (68930153/100000000000000 : ℝ)*(upper5) + (335744763973103/10000000000000 : ℝ)*(major0) + (335744763973103/10000000000000 : ℝ)*(major1) + (335744763973103/10000000000000 : ℝ)*(major2) + (4667891711667459/100000000000000 : ℝ)*(sp0) + (583487935469031/12500000000000 : ℝ)*(sp1) + (4667903527473293/100000000000000 : ℝ)*(sp2) + (20469840348019/1000000000000 : ℝ)*(sp3) + (12598345411/100000000000000 : ℝ)*(sp4) + (6766332821/100000000000000 : ℝ)*(sp7) + (2046990801134721/100000000000000 : ℝ)*(f.failure) + (466790431001287/10000000000000 : ℝ)*(f.sum) + (9924586308577/2275000000000000000000000000 : ℝ)*base65 + (19198496699474711/3250000000000000000000000000000 : ℝ)*base67 + (2323634935974711/3250000000000000000000000000000 : ℝ)*base69 + (10876983407275289/3250000000000000000000000000000 : ℝ)*base72 + (11743075208077/2275000000000000000000000000 : ℝ)*base73 + (7245623127224711/3250000000000000000000000000000 : ℝ)*base75 + (29227203663724711/3250000000000000000000000000000 : ℝ)*base77 + (6403724097275289/3250000000000000000000000000000 : ℝ)*base80 + (5526225176623/2275000000000000000000000000 : ℝ)*base82 + (59878537/10000000000000000000000 : ℝ)*base89 + (59878537/10000000000000000000000 : ℝ)*base91 + (59878537/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56780842990037078672757/5687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (228213659/10000000000000 : ℝ)*(base19) + (2400816967/100000000000000 : ℝ)*(base23) + (3767149/400000000000 : ℝ)*(lower1) + (28814627/10000000000000 : ℝ)*(upper3) + (16212173/100000000000000 : ℝ)*(lower4) + (36145769/25000000000000 : ℝ)*(upper5) + (1696262333104793/50000000000000 : ℝ)*(major0) + (1696262333104793/50000000000000 : ℝ)*(major1) + (1696262333104793/50000000000000 : ℝ)*(major2) + (6103202881/100000000000000 : ℝ)*(sp2) + (4716672205856903/100000000000000 : ℝ)*(sp4) + (4716669923720313/100000000000000 : ℝ)*(sp5) + (2358331850918527/50000000000000 : ℝ)*(sp6) + (517094198445191/25000000000000 : ℝ)*(sp7) + (517094198445191/25000000000000 : ℝ)*(f.failure) + (4716672205856903/100000000000000 : ℝ)*(f.sum) + (21876862747287/11375000000000000000000000000 : ℝ)*base65 + (87178316085324241/16250000000000000000000000000000 : ℝ)*base67 + (98925088853425759/16250000000000000000000000000000 : ℝ)*base70 + (150557072955324241/16250000000000000000000000000000 : ℝ)*base71 + (22575023961037/11375000000000000000000000000 : ℝ)*base73 + (428752324594675759/16250000000000000000000000000000 : ℝ)*base76 + (8676543369074241/16250000000000000000000000000000 : ℝ)*base77 + (121719296165925759/16250000000000000000000000000000 : ℝ)*base80 + (64791300243213/11375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3736127/2500000000000000000000 : ℝ)*base89 + (3736127/2500000000000000000000 : ℝ)*base91 + (3736127/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1520_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (547/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1520_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1520_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15967/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1520_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1520_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1520_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4535/1024 : ℝ) ≤ p) (hpb : p ≤ (4537/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164018697/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15967/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5473/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1520_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
