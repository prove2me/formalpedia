-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1644_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:23.316441+00:00
-- url     : https://prove2.me/submissions/1ff2e58f-ad7f-4e30-a114-debb88119b0a

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
theorem support_rectangle_w1644_s0_0 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-75162187/500000000 : ℝ)*x 0 + (5792779509/10000000000 : ℝ)*x 1 + (2458727387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75162187/500000000 : ℝ)^4895 ≤ (9106008747179/100000000000000 : ℝ)^3871 := by
    have hnat : (75162187 : ℕ)^4895*100000000000000^3871 ≤ 9106008747179^3871*500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75162187 500000000 9106008747179 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5792779509/10000000000 : ℝ)^4895 ≤ (10027512773027/20000000000000 : ℝ)^3871 := by
    have hnat : (5792779509 : ℕ)^4895*20000000000000^3871 ≤ 10027512773027^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5792779509 10000000000 10027512773027 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2458727387/5000000000 : ℝ)^4895 ≤ (40756427374201/100000000000000 : ℝ)^3871 := by
    have hnat : (2458727387 : ℕ)^4895*100000000000000^3871 ≤ 40756427374201^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458727387 5000000000 40756427374201 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-75162187/500000000 : ℝ), (5792779509/10000000000 : ℝ), (2458727387/5000000000 : ℝ)] ![(9106008747179/100000000000000 : ℝ), (10027512773027/20000000000000 : ℝ), (40756427374201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-75162187/500000000 : ℝ)|^4895 ≤ (9106008747179/100000000000000 : ℝ)^3871
        have hw : |(-75162187/500000000 : ℝ)|=(75162187/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5792779509/10000000000 : ℝ)|^4895 ≤ (10027512773027/20000000000000 : ℝ)^3871
        have hw : |(5792779509/10000000000 : ℝ)|=(5792779509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2458727387/5000000000 : ℝ)|^4895 ≤ (40756427374201/100000000000000 : ℝ)^3871
        have hw : |(2458727387/5000000000 : ℝ)|=(2458727387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s0_1 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5439921979/10000000000 : ℝ)*x 0 + (-1984332003/10000000000 : ℝ)*x 1 + (2458727967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5439921979/10000000000 : ℝ)^4895 ≤ (1852288767181/4000000000000 : ℝ)^3871 := by
    have hnat : (5439921979 : ℕ)^4895*4000000000000^3871 ≤ 1852288767181^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439921979 10000000000 1852288767181 4000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1984332003/10000000000 : ℝ)^4895 ≤ (12936341275189/100000000000000 : ℝ)^3871 := by
    have hnat : (1984332003 : ℕ)^4895*100000000000000^3871 ≤ 12936341275189^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984332003 10000000000 12936341275189 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2458727967/5000000000 : ℝ)^4895 ≤ (40756439531673/100000000000000 : ℝ)^3871 := by
    have hnat : (2458727967 : ℕ)^4895*100000000000000^3871 ≤ 40756439531673^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458727967 5000000000 40756439531673 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5439921979/10000000000 : ℝ), (-1984332003/10000000000 : ℝ), (2458727967/5000000000 : ℝ)] ![(1852288767181/4000000000000 : ℝ), (12936341275189/100000000000000 : ℝ), (40756439531673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5439921979/10000000000 : ℝ)|^4895 ≤ (1852288767181/4000000000000 : ℝ)^3871
        have hw : |(5439921979/10000000000 : ℝ)|=(5439921979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1984332003/10000000000 : ℝ)|^4895 ≤ (12936341275189/100000000000000 : ℝ)^3871
        have hw : |(-1984332003/10000000000 : ℝ)|=(1984332003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2458727967/5000000000 : ℝ)|^4895 ≤ (40756439531673/100000000000000 : ℝ)^3871
        have hw : |(2458727967/5000000000 : ℝ)|=(2458727967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s0_2 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5439924167/10000000000 : ℝ)*x 0 + (983490891/2000000000 : ℝ)*x 1 + (-992165513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5439924167/10000000000 : ℝ)^4895 ≤ (46307242731801/100000000000000 : ℝ)^3871 := by
    have hnat : (5439924167 : ℕ)^4895*100000000000000^3871 ≤ 46307242731801^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439924167 10000000000 46307242731801 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983490891/2000000000 : ℝ)^4895 ≤ (2547276501931/6250000000000 : ℝ)^3871 := by
    have hnat : (983490891 : ℕ)^4895*6250000000000^3871 ≤ 2547276501931^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983490891 2000000000 2547276501931 6250000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992165513/5000000000 : ℝ)^4895 ≤ (12936333221011/100000000000000 : ℝ)^3871 := by
    have hnat : (992165513 : ℕ)^4895*100000000000000^3871 ≤ 12936333221011^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992165513 5000000000 12936333221011 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5439924167/10000000000 : ℝ), (983490891/2000000000 : ℝ), (-992165513/5000000000 : ℝ)] ![(46307242731801/100000000000000 : ℝ), (2547276501931/6250000000000 : ℝ), (12936333221011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5439924167/10000000000 : ℝ)|^4895 ≤ (46307242731801/100000000000000 : ℝ)^3871
        have hw : |(5439924167/10000000000 : ℝ)|=(5439924167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(983490891/2000000000 : ℝ)|^4895 ≤ (2547276501931/6250000000000 : ℝ)^3871
        have hw : |(983490891/2000000000 : ℝ)|=(983490891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992165513/5000000000 : ℝ)|^4895 ≤ (12936333221011/100000000000000 : ℝ)^3871
        have hw : |(-992165513/5000000000 : ℝ)|=(992165513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s0_3 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (255839449/625000000 : ℝ)*x 0 + (3081154209/10000000000 : ℝ)*x 1 + (1065744971/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255839449/625000000 : ℝ)^4895 ≤ (1010002810309/3125000000000 : ℝ)^3871 := by
    have hnat : (255839449 : ℕ)^4895*3125000000000^3871 ≤ 1010002810309^3871*625000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255839449 625000000 1010002810309 3125000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3081154209/10000000000 : ℝ)^4895 ≤ (2256639691891/10000000000000 : ℝ)^3871 := by
    have hnat : (3081154209 : ℕ)^4895*10000000000000^3871 ≤ 2256639691891^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3081154209 10000000000 2256639691891 10000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065744971/2000000000 : ℝ)^4895 ≤ (11278378282657/25000000000000 : ℝ)^3871 := by
    have hnat : (1065744971 : ℕ)^4895*25000000000000^3871 ≤ 11278378282657^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065744971 2000000000 11278378282657 25000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(255839449/625000000 : ℝ), (3081154209/10000000000 : ℝ), (1065744971/2000000000 : ℝ)] ![(1010002810309/3125000000000 : ℝ), (2256639691891/10000000000000 : ℝ), (11278378282657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(255839449/625000000 : ℝ)|^4895 ≤ (1010002810309/3125000000000 : ℝ)^3871
        have hw : |(255839449/625000000 : ℝ)|=(255839449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3081154209/10000000000 : ℝ)|^4895 ≤ (2256639691891/10000000000000 : ℝ)^3871
        have hw : |(3081154209/10000000000 : ℝ)|=(3081154209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1065744971/2000000000 : ℝ)|^4895 ≤ (11278378282657/25000000000000 : ℝ)^3871
        have hw : |(1065744971/2000000000 : ℝ)|=(1065744971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s0_4 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-752804501/5000000000 : ℝ)*x 0 + (987847627/2000000000 : ℝ)*x 1 + (2885120213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (752804501/5000000000 : ℝ)^4895 ≤ (4562065199379/50000000000000 : ℝ)^3871 := by
    have hnat : (752804501 : ℕ)^4895*50000000000000^3871 ≤ 4562065199379^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752804501 5000000000 4562065199379 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987847627/2000000000 : ℝ)^4895 ≤ (8196972644069/20000000000000 : ℝ)^3871 := by
    have hnat : (987847627 : ℕ)^4895*20000000000000^3871 ≤ 8196972644069^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987847627 2000000000 8196972644069 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2885120213/5000000000 : ℝ)^4895 ≤ (49891006361063/100000000000000 : ℝ)^3871 := by
    have hnat : (2885120213 : ℕ)^4895*100000000000000^3871 ≤ 49891006361063^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885120213 5000000000 49891006361063 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-752804501/5000000000 : ℝ), (987847627/2000000000 : ℝ), (2885120213/5000000000 : ℝ)] ![(4562065199379/50000000000000 : ℝ), (8196972644069/20000000000000 : ℝ), (49891006361063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-752804501/5000000000 : ℝ)|^4895 ≤ (4562065199379/50000000000000 : ℝ)^3871
        have hw : |(-752804501/5000000000 : ℝ)|=(752804501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(987847627/2000000000 : ℝ)|^4895 ≤ (8196972644069/20000000000000 : ℝ)^3871
        have hw : |(987847627/2000000000 : ℝ)|=(987847627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2885120213/5000000000 : ℝ)|^4895 ≤ (49891006361063/100000000000000 : ℝ)^3871
        have hw : |(2885120213/5000000000 : ℝ)|=(2885120213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s0_5 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208040851/400000000 : ℝ)*x 0 + (-565773231/5000000000 : ℝ)*x 1 + (1154048011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208040851/400000000 : ℝ)^4895 ≤ (43750723081707/100000000000000 : ℝ)^3871 := by
    have hnat : (208040851 : ℕ)^4895*100000000000000^3871 ≤ 43750723081707^3871*400000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208040851 400000000 43750723081707 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565773231/5000000000 : ℝ)^4895 ≤ (158956865049/2500000000000 : ℝ)^3871 := by
    have hnat : (565773231 : ℕ)^4895*2500000000000^3871 ≤ 158956865049^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565773231 5000000000 158956865049 2500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1154048011/2000000000 : ℝ)^4895 ≤ (49891002304747/100000000000000 : ℝ)^3871 := by
    have hnat : (1154048011 : ℕ)^4895*100000000000000^3871 ≤ 49891002304747^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154048011 2000000000 49891002304747 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208040851/400000000 : ℝ), (-565773231/5000000000 : ℝ), (1154048011/2000000000 : ℝ)] ![(43750723081707/100000000000000 : ℝ), (158956865049/2500000000000 : ℝ), (49891002304747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208040851/400000000 : ℝ)|^4895 ≤ (43750723081707/100000000000000 : ℝ)^3871
        have hw : |(208040851/400000000 : ℝ)|=(208040851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-565773231/5000000000 : ℝ)|^4895 ≤ (158956865049/2500000000000 : ℝ)^3871
        have hw : |(-565773231/5000000000 : ℝ)|=(565773231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1154048011/2000000000 : ℝ)|^4895 ≤ (49891002304747/100000000000000 : ℝ)^3871
        have hw : |(1154048011/2000000000 : ℝ)|=(1154048011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s0_6 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201020883/10000000000 : ℝ)*x 0 + (5770240651/10000000000 : ℝ)*x 1 + (-1131546131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201020883/10000000000 : ℝ)^4895 ≤ (683604982999/1562500000000 : ℝ)^3871 := by
    have hnat : (5201020883 : ℕ)^4895*1562500000000^3871 ≤ 683604982999^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201020883 10000000000 683604982999 1562500000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5770240651/10000000000 : ℝ)^4895 ≤ (49891008821093/100000000000000 : ℝ)^3871 := by
    have hnat : (5770240651 : ℕ)^4895*100000000000000^3871 ≤ 49891008821093^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5770240651 10000000000 49891008821093 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131546131/10000000000 : ℝ)^4895 ≤ (635827225003/10000000000000 : ℝ)^3871 := by
    have hnat : (1131546131 : ℕ)^4895*10000000000000^3871 ≤ 635827225003^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131546131 10000000000 635827225003 10000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201020883/10000000000 : ℝ), (5770240651/10000000000 : ℝ), (-1131546131/10000000000 : ℝ)] ![(683604982999/1562500000000 : ℝ), (49891008821093/100000000000000 : ℝ), (635827225003/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201020883/10000000000 : ℝ)|^4895 ≤ (683604982999/1562500000000 : ℝ)^3871
        have hw : |(5201020883/10000000000 : ℝ)|=(5201020883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5770240651/10000000000 : ℝ)|^4895 ≤ (49891008821093/100000000000000 : ℝ)^3871
        have hw : |(5770240651/10000000000 : ℝ)|=(5770240651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1131546131/10000000000 : ℝ)|^4895 ≤ (635827225003/10000000000000 : ℝ)^3871
        have hw : |(-1131546131/10000000000 : ℝ)|=(1131546131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s0_7 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2049753901/5000000000 : ℝ)*x 0 + (1054558463/2000000000 : ℝ)*x 1 + (3139023523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049753901/5000000000 : ℝ)^4895 ≤ (3238077219169/10000000000000 : ℝ)^3871 := by
    have hnat : (2049753901 : ℕ)^4895*10000000000000^3871 ≤ 3238077219169^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049753901 5000000000 3238077219169 10000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054558463/2000000000 : ℝ)^4895 ≤ (22257776311857/50000000000000 : ℝ)^3871 := by
    have hnat : (1054558463 : ℕ)^4895*50000000000000^3871 ≤ 22257776311857^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054558463 2000000000 22257776311857 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3139023523/10000000000 : ℝ)^4895 ≤ (23103675163863/100000000000000 : ℝ)^3871 := by
    have hnat : (3139023523 : ℕ)^4895*100000000000000^3871 ≤ 23103675163863^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3139023523 10000000000 23103675163863 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2049753901/5000000000 : ℝ), (1054558463/2000000000 : ℝ), (3139023523/10000000000 : ℝ)] ![(3238077219169/10000000000000 : ℝ), (22257776311857/50000000000000 : ℝ), (23103675163863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2049753901/5000000000 : ℝ)|^4895 ≤ (3238077219169/10000000000000 : ℝ)^3871
        have hw : |(2049753901/5000000000 : ℝ)|=(2049753901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054558463/2000000000 : ℝ)|^4895 ≤ (22257776311857/50000000000000 : ℝ)^3871
        have hw : |(1054558463/2000000000 : ℝ)|=(1054558463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3139023523/10000000000 : ℝ)|^4895 ≤ (23103675163863/100000000000000 : ℝ)^3871
        have hw : |(3139023523/10000000000 : ℝ)|=(3139023523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1644_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4727/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4697/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4891/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4891 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4891*1^1024 ≤ 0^1024*1^4891 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4891 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4891/1024 : ℝ) ≤ (1256875903076622059/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4891 ≤ (1256875903076622059/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4891*100000000000000000000^1024 ≤ 1256875903076622059^1024*5^4891 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1256875903076622059 100000000000000000000 4891 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1256875903076622059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4891 := by
      have hnat : (1 : ℕ)^1024*1^4891 ≤ 1^4891*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101256875903076622059/100000000000000000000 : ℝ) ≤ (501309234940797/500000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (101256875903076622059/100000000000000000000 : ℝ)^1024 ≤ (501309234940797/500000000000000 : ℝ)^4891 := by
      have hnat : (101256875903076622059 : ℕ)^1024*500000000000000^4891 ≤ 501309234940797^4891*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101256875903076622059 100000000000000000000 501309234940797 500000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501309234940797/500000000000000 : ℝ)) (X := (101256875903076622059/100000000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51256875903076622059/50000000000000000000 : ℝ) ≤ (251309234940797/250000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (51256875903076622059/50000000000000000000 : ℝ)^1024 ≤ (251309234940797/250000000000000 : ℝ)^4891 := by
      have hnat : (51256875903076622059 : ℕ)^1024*250000000000000^4891 ≤ 251309234940797^4891*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51256875903076622059 50000000000000000000 251309234940797 250000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251309234940797/250000000000000 : ℝ)) (X := (51256875903076622059/50000000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1309234940797/200000000000000 : ℝ)*(0 : ℝ))^(4891/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1309234940797/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1256875903076622059/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1309234940797/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4891/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1309234940797/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(501309234940797/500000000000000 : ℝ) by norm_num, show 1+(1256875903076622059/100000000000000000000 : ℝ)+(0 : ℝ)=(101256875903076622059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1256875903076622059/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1309234940797/200000000000000 : ℝ)*(2/5 : ℝ))^(4891/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1309234940797/200000000000000 : ℝ)*(2/5 : ℝ)=(251309234940797/250000000000000 : ℝ) by norm_num, show 1+2*(1256875903076622059/100000000000000000000 : ℝ)=(51256875903076622059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1309234940797/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1309234940797/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1309234940797/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1309234940797/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1309234940797/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1309234940797/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-75162187/500000000 : ℝ)*X 0 0+(5792779509/10000000000 : ℝ)*X 0 1+(2458727387/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5439921979/10000000000 : ℝ)*X 1 0+(-1984332003/10000000000 : ℝ)*X 1 1+(2458727967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5439924167/10000000000 : ℝ)*X 2 0+(983490891/2000000000 : ℝ)*X 2 1+(-992165513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((255839449/625000000 : ℝ)*X 0 0+(3081154209/10000000000 : ℝ)*X 0 1+(1065744971/2000000000 : ℝ)*X 0 2+(255839449/625000000 : ℝ)*X 1 0+(3081154209/10000000000 : ℝ)*X 1 1+(1065744971/2000000000 : ℝ)*X 1 2+(255839449/625000000 : ℝ)*X 2 0+(3081154209/10000000000 : ℝ)*X 2 1+(1065744971/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-752804501/5000000000 : ℝ)*X 0 0+(987847627/2000000000 : ℝ)*X 0 1+(2885120213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((208040851/400000000 : ℝ)*X 1 0+(-565773231/5000000000 : ℝ)*X 1 1+(1154048011/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5201020883/10000000000 : ℝ)*X 2 0+(5770240651/10000000000 : ℝ)*X 2 1+(-1131546131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2049753901/5000000000 : ℝ)*X 0 0+(1054558463/2000000000 : ℝ)*X 0 1+(3139023523/10000000000 : ℝ)*X 0 2+(2049753901/5000000000 : ℝ)*X 1 0+(1054558463/2000000000 : ℝ)*X 1 1+(3139023523/10000000000 : ℝ)*X 1 2+(2049753901/5000000000 : ℝ)*X 2 0+(1054558463/2000000000 : ℝ)*X 2 1+(3139023523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (557864113022278421169/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (446915921/100000000000000 : ℝ)*(base19) + (643240129/100000000000000 : ℝ)*(base23) + (1930109/5000000000000 : ℝ)*(base24) + (122167347/100000000000000 : ℝ)*(upper4) + (107109/80000000000 : ℝ)*(upper5) + (9921032031553/1250000000000 : ℝ)*(major0) + (9921032031553/1250000000000 : ℝ)*(major1) + (9921032031553/1250000000000 : ℝ)*(major2) + (285608655940429/25000000000000 : ℝ)*(sp0) + (1142438394434243/100000000000000 : ℝ)*(sp1) + (71402384969241/6250000000000 : ℝ)*(sp2) + (111231375222359/25000000000000 : ℝ)*(sp3) + (131799639/3125000000000 : ℝ)*(sp4) + (79255639/12500000000000 : ℝ)*(sp7) + (111231533733637/25000000000000 : ℝ)*(f.failure) + (285609710337541/25000000000000 : ℝ)*(f.sum) + (225857303741/125000000000000000000000000 : ℝ)*base65 + (1050532114259/250000000000000000000000000 : ℝ)*base68 + (190942129259/250000000000000000000000000 : ℝ)*base70 + (360475231491/250000000000000000000000000 : ℝ)*base71 + (247952745817/62500000000000000000000000 : ℝ)*base74 + (1128521361759/250000000000000000000000000 : ℝ)*base76 + (1368232032259/250000000000000000000000000 : ℝ)*base78 + (2064071253259/250000000000000000000000000 : ℝ)*base80 + (552379169759/125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (107423/1250000000000000000000 : ℝ)*base90 + (107423/1250000000000000000000 : ℝ)*base92 + (107423/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24707448023123867049519/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (515227257/50000000000000 : ℝ)*(base19) + (194018273/20000000000000 : ℝ)*(base23) + (70631179/100000000000000 : ℝ)*(base32) + (197499017/100000000000000 : ℝ)*(upper3) + (141764563/100000000000000 : ℝ)*(upper5) + (836009980986003/100000000000000 : ℝ)*(major0) + (836009980986003/100000000000000 : ℝ)*(major1) + (836009980986003/100000000000000 : ℝ)*(major2) + (35492871/1562500000000 : ℝ)*(sp1) + (1465953689/50000000000000 : ℝ)*(sp2) + (1203365568008393/100000000000000 : ℝ)*(sp4) + (240672453202027/20000000000000 : ℝ)*(sp5) + (1203361666009649/100000000000000 : ℝ)*(sp6) + (234327079308053/50000000000000 : ℝ)*(sp7) + (117163557311821/25000000000000 : ℝ)*(f.failure) + (1203365568008393/100000000000000 : ℝ)*(f.sum) + (12841661595609/10000000000000000000000000000 : ℝ)*base66 + (238420458235609/20000000000000000000000000000 : ℝ)*base68 + (78397746455609/20000000000000000000000000000 : ℝ)*base70 + (145587219595609/20000000000000000000000000000 : ℝ)*base72 + (51296547215609/10000000000000000000000000000 : ℝ)*base74 + (32206524515609/20000000000000000000000000000 : ℝ)*base76 + (64989873435609/20000000000000000000000000000 : ℝ)*base78 + (8537326915609/20000000000000000000000000000 : ℝ)*base80 + (7289945245609/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8227159/1250000000000000000000 : ℝ)*base90 + (8227159/1250000000000000000000 : ℝ)*base92 + (8227159/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1644_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4727/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4697/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1644_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1644_s1_0 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-20145271/125000000 : ℝ)*x 0 + (1100170121/2000000000 : ℝ)*x 1 + (5138996141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20145271/125000000 : ℝ)^4895 ≤ (497198166603/5000000000000 : ℝ)^3871 := by
    have hnat : (20145271 : ℕ)^4895*5000000000000^3871 ≤ 497198166603^3871*125000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20145271 125000000 497198166603 5000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100170121/2000000000 : ℝ)^4895 ≤ (5870505220447/12500000000000 : ℝ)^3871 := by
    have hnat : (1100170121 : ℕ)^4895*12500000000000^3871 ≤ 5870505220447^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100170121 2000000000 5870505220447 12500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138996141/10000000000 : ℝ)^4895 ≤ (43091994886501/100000000000000 : ℝ)^3871 := by
    have hnat : (5138996141 : ℕ)^4895*100000000000000^3871 ≤ 43091994886501^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138996141 10000000000 43091994886501 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20145271/125000000 : ℝ), (1100170121/2000000000 : ℝ), (5138996141/10000000000 : ℝ)] ![(497198166603/5000000000000 : ℝ), (5870505220447/12500000000000 : ℝ), (43091994886501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20145271/125000000 : ℝ)|^4895 ≤ (497198166603/5000000000000 : ℝ)^3871
        have hw : |(-20145271/125000000 : ℝ)|=(20145271/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100170121/2000000000 : ℝ)|^4895 ≤ (5870505220447/12500000000000 : ℝ)^3871
        have hw : |(1100170121/2000000000 : ℝ)|=(1100170121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138996141/10000000000 : ℝ)|^4895 ≤ (43091994886501/100000000000000 : ℝ)^3871
        have hw : |(5138996141/10000000000 : ℝ)|=(5138996141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s1_1 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340569007/2500000000 : ℝ)*x 0 + (-1799893751/10000000000 : ℝ)*x 1 + (2569497979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340569007/2500000000 : ℝ)^4895 ≤ (2842062423377/6250000000000 : ℝ)^3871 := by
    have hnat : (1340569007 : ℕ)^4895*6250000000000^3871 ≤ 2842062423377^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340569007 2500000000 2842062423377 6250000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799893751/10000000000 : ℝ)^4895 ≤ (2287001652191/20000000000000 : ℝ)^3871 := by
    have hnat : (1799893751 : ℕ)^4895*20000000000000^3871 ≤ 2287001652191^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799893751 10000000000 2287001652191 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569497979/5000000000 : ℝ)^4895 ≤ (43091992946067/100000000000000 : ℝ)^3871 := by
    have hnat : (2569497979 : ℕ)^4895*100000000000000^3871 ≤ 43091992946067^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569497979 5000000000 43091992946067 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340569007/2500000000 : ℝ), (-1799893751/10000000000 : ℝ), (2569497979/5000000000 : ℝ)] ![(2842062423377/6250000000000 : ℝ), (2287001652191/20000000000000 : ℝ), (43091992946067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340569007/2500000000 : ℝ)|^4895 ≤ (2842062423377/6250000000000 : ℝ)^3871
        have hw : |(1340569007/2500000000 : ℝ)|=(1340569007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1799893751/10000000000 : ℝ)|^4895 ≤ (2287001652191/20000000000000 : ℝ)^3871
        have hw : |(-1799893751/10000000000 : ℝ)|=(1799893751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569497979/5000000000 : ℝ)|^4895 ≤ (43091992946067/100000000000000 : ℝ)^3871
        have hw : |(2569497979/5000000000 : ℝ)|=(2569497979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s1_2 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072455431/2000000000 : ℝ)*x 0 + (2569497337/5000000000 : ℝ)*x 1 + (-899946971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072455431/2000000000 : ℝ)^4895 ≤ (9094602171869/20000000000000 : ℝ)^3871 := by
    have hnat : (1072455431 : ℕ)^4895*20000000000000^3871 ≤ 9094602171869^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072455431 2000000000 9094602171869 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569497337/5000000000 : ℝ)^4895 ≤ (21545989665609/50000000000000 : ℝ)^3871 := by
    have hnat : (2569497337 : ℕ)^4895*50000000000000^3871 ≤ 21545989665609^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569497337 5000000000 21545989665609 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899946971/5000000000 : ℝ)^4895 ≤ (2858752448851/25000000000000 : ℝ)^3871 := by
    have hnat : (899946971 : ℕ)^4895*25000000000000^3871 ≤ 2858752448851^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899946971 5000000000 2858752448851 25000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072455431/2000000000 : ℝ), (2569497337/5000000000 : ℝ), (-899946971/5000000000 : ℝ)] ![(9094602171869/20000000000000 : ℝ), (21545989665609/50000000000000 : ℝ), (2858752448851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072455431/2000000000 : ℝ)|^4895 ≤ (9094602171869/20000000000000 : ℝ)^3871
        have hw : |(1072455431/2000000000 : ℝ)|=(1072455431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569497337/5000000000 : ℝ)|^4895 ≤ (21545989665609/50000000000000 : ℝ)^3871
        have hw : |(2569497337/5000000000 : ℝ)|=(2569497337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-899946971/5000000000 : ℝ)|^4895 ≤ (2858752448851/25000000000000 : ℝ)^3871
        have hw : |(-899946971/5000000000 : ℝ)|=(899946971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s1_3 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2088735997/5000000000 : ℝ)*x 0 + (3731758721/10000000000 : ℝ)*x 1 + (2330448007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088735997/5000000000 : ℝ)^4895 ≤ (414517998689/1250000000000 : ℝ)^3871 := by
    have hnat : (2088735997 : ℕ)^4895*1250000000000^3871 ≤ 414517998689^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088735997 5000000000 414517998689 1250000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3731758721/10000000000 : ℝ)^4895 ≤ (5750443780417/20000000000000 : ℝ)^3871 := by
    have hnat : (3731758721 : ℕ)^4895*20000000000000^3871 ≤ 5750443780417^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731758721 10000000000 5750443780417 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2330448007/5000000000 : ℝ)^4895 ≤ (19043170591467/50000000000000 : ℝ)^3871 := by
    have hnat : (2330448007 : ℕ)^4895*50000000000000^3871 ≤ 19043170591467^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2330448007 5000000000 19043170591467 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088735997/5000000000 : ℝ), (3731758721/10000000000 : ℝ), (2330448007/5000000000 : ℝ)] ![(414517998689/1250000000000 : ℝ), (5750443780417/20000000000000 : ℝ), (19043170591467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088735997/5000000000 : ℝ)|^4895 ≤ (414517998689/1250000000000 : ℝ)^3871
        have hw : |(2088735997/5000000000 : ℝ)|=(2088735997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3731758721/10000000000 : ℝ)|^4895 ≤ (5750443780417/20000000000000 : ℝ)^3871
        have hw : |(3731758721/10000000000 : ℝ)|=(3731758721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2330448007/5000000000 : ℝ)|^4895 ≤ (19043170591467/50000000000000 : ℝ)^3871
        have hw : |(2330448007/5000000000 : ℝ)|=(2330448007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s1_4 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1611786741/10000000000 : ℝ)*x 0 + (2571351379/5000000000 : ℝ)*x 1 + (5497090131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1611786741/10000000000 : ℝ)^4895 ≤ (9945251214711/100000000000000 : ℝ)^3871 := by
    have hnat : (1611786741 : ℕ)^4895*100000000000000^3871 ≤ 9945251214711^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611786741 10000000000 9945251214711 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571351379/5000000000 : ℝ)^4895 ≤ (21565650810639/50000000000000 : ℝ)^3871 := by
    have hnat : (2571351379 : ℕ)^4895*50000000000000^3871 ≤ 21565650810639^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571351379 5000000000 21565650810639 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497090131/10000000000 : ℝ)^4895 ≤ (46923447146083/100000000000000 : ℝ)^3871 := by
    have hnat : (5497090131 : ℕ)^4895*100000000000000^3871 ≤ 46923447146083^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497090131 10000000000 46923447146083 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1611786741/10000000000 : ℝ), (2571351379/5000000000 : ℝ), (5497090131/10000000000 : ℝ)] ![(9945251214711/100000000000000 : ℝ), (21565650810639/50000000000000 : ℝ), (46923447146083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1611786741/10000000000 : ℝ)|^4895 ≤ (9945251214711/100000000000000 : ℝ)^3871
        have hw : |(-1611786741/10000000000 : ℝ)|=(1611786741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571351379/5000000000 : ℝ)|^4895 ≤ (21565650810639/50000000000000 : ℝ)^3871
        have hw : |(2571351379/5000000000 : ℝ)|=(2571351379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497090131/10000000000 : ℝ)|^4895 ≤ (46923447146083/100000000000000 : ℝ)^3871
        have hw : |(5497090131/10000000000 : ℝ)|=(5497090131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s1_5 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210623461/400000000 : ℝ)*x 0 + (-1441799089/10000000000 : ℝ)*x 1 + (1099418027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210623461/400000000 : ℝ)^4895 ≤ (44438638925179/100000000000000 : ℝ)^3871 := by
    have hnat : (210623461 : ℕ)^4895*100000000000000^3871 ≤ 44438638925179^3871*400000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210623461 400000000 44438638925179 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1441799089/10000000000 : ℝ)^4895 ≤ (8637913882161/100000000000000 : ℝ)^3871 := by
    have hnat : (1441799089 : ℕ)^4895*100000000000000^3871 ≤ 8637913882161^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441799089 10000000000 8637913882161 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099418027/2000000000 : ℝ)^4895 ≤ (46923447189259/100000000000000 : ℝ)^3871 := by
    have hnat : (1099418027 : ℕ)^4895*100000000000000^3871 ≤ 46923447189259^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099418027 2000000000 46923447189259 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210623461/400000000 : ℝ), (-1441799089/10000000000 : ℝ), (1099418027/2000000000 : ℝ)] ![(44438638925179/100000000000000 : ℝ), (8637913882161/100000000000000 : ℝ), (46923447189259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210623461/400000000 : ℝ)|^4895 ≤ (44438638925179/100000000000000 : ℝ)^3871
        have hw : |(210623461/400000000 : ℝ)|=(210623461/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1441799089/10000000000 : ℝ)|^4895 ≤ (8637913882161/100000000000000 : ℝ)^3871
        have hw : |(-1441799089/10000000000 : ℝ)|=(1441799089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099418027/2000000000 : ℝ)|^4895 ≤ (46923447189259/100000000000000 : ℝ)^3871
        have hw : |(1099418027/2000000000 : ℝ)|=(1099418027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s1_6 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316396591/2500000000 : ℝ)*x 0 + (1374272593/2500000000 : ℝ)*x 1 + (-22528109/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316396591/2500000000 : ℝ)^4895 ≤ (44438637206997/100000000000000 : ℝ)^3871 := by
    have hnat : (1316396591 : ℕ)^4895*100000000000000^3871 ≤ 44438637206997^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316396591 2500000000 44438637206997 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374272593/2500000000 : ℝ)^4895 ≤ (23461724873731/50000000000000 : ℝ)^3871 := by
    have hnat : (1374272593 : ℕ)^4895*50000000000000^3871 ≤ 23461724873731^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374272593 2500000000 23461724873731 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22528109/156250000 : ℝ)^4895 ≤ (1727582605217/20000000000000 : ℝ)^3871 := by
    have hnat : (22528109 : ℕ)^4895*20000000000000^3871 ≤ 1727582605217^3871*156250000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22528109 156250000 1727582605217 20000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316396591/2500000000 : ℝ), (1374272593/2500000000 : ℝ), (-22528109/156250000 : ℝ)] ![(44438637206997/100000000000000 : ℝ), (23461724873731/50000000000000 : ℝ), (1727582605217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316396591/2500000000 : ℝ)|^4895 ≤ (44438637206997/100000000000000 : ℝ)^3871
        have hw : |(1316396591/2500000000 : ℝ)|=(1316396591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374272593/2500000000 : ℝ)|^4895 ≤ (23461724873731/50000000000000 : ℝ)^3871
        have hw : |(1374272593/2500000000 : ℝ)|=(1374272593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22528109/156250000 : ℝ)|^4895 ≤ (1727582605217/20000000000000 : ℝ)^3871
        have hw : |(-22528109/156250000 : ℝ)|=(22528109/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s1_7 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044473069/2500000000 : ℝ)*x 0 + (465137721/1000000000 : ℝ)*x 1 + (374141509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044473069/2500000000 : ℝ)^4895 ≤ (4145707345377/12500000000000 : ℝ)^3871 := by
    have hnat : (1044473069 : ℕ)^4895*12500000000000^3871 ≤ 4145707345377^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044473069 2500000000 4145707345377 12500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465137721/1000000000 : ℝ)^4895 ≤ (37988009298533/100000000000000 : ℝ)^3871 := by
    have hnat : (465137721 : ℕ)^4895*100000000000000^3871 ≤ 37988009298533^3871*1000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465137721 1000000000 37988009298533 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374141509/1000000000 : ℝ)^4895 ≤ (2884633192143/10000000000000 : ℝ)^3871 := by
    have hnat : (374141509 : ℕ)^4895*10000000000000^3871 ≤ 2884633192143^3871*1000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374141509 1000000000 2884633192143 10000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044473069/2500000000 : ℝ), (465137721/1000000000 : ℝ), (374141509/1000000000 : ℝ)] ![(4145707345377/12500000000000 : ℝ), (37988009298533/100000000000000 : ℝ), (2884633192143/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044473069/2500000000 : ℝ)|^4895 ≤ (4145707345377/12500000000000 : ℝ)^3871
        have hw : |(1044473069/2500000000 : ℝ)|=(1044473069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(465137721/1000000000 : ℝ)|^4895 ≤ (37988009298533/100000000000000 : ℝ)^3871
        have hw : |(465137721/1000000000 : ℝ)|=(465137721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(374141509/1000000000 : ℝ)|^4895 ≤ (2884633192143/10000000000000 : ℝ)^3871
        have hw : |(374141509/1000000000 : ℝ)|=(374141509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1644_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4697/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4837/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17359/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4697/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4727/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4697/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4727/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4697/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4727/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4697/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4727/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4697/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4727/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4697/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4727/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4727/100000 : ℝ) ^ (4891/1024 : ℝ) ≤ (23350929107243/50000000000000000000 : ℝ) := by
    have hpowers : (4727/100000 : ℝ)^4891 ≤ (23350929107243/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4727 : ℕ)^4891*50000000000000000000^1024 ≤ 23350929107243^1024*100000^4891 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4727 100000 23350929107243 50000000000000000000 4891 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4727/100000 : ℝ)) (X := (23350929107243/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4697/20000 : ℝ) ^ (4891/1024 : ℝ) ≤ (24694754155701967/25000000000000000000 : ℝ) := by
    have hpowers : (4697/20000 : ℝ)^4891 ≤ (24694754155701967/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4697 : ℕ)^4891*25000000000000000000^1024 ≤ 24694754155701967^1024*20000^4891 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4697 20000 24694754155701967 25000000000000000000 4891 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4697/20000 : ℝ)) (X := (24694754155701967/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000023350929107243/25000000000000000000 : ℝ) ≤ (5000000977769069/5000000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (25000023350929107243/25000000000000000000 : ℝ)^1024 ≤ (5000000977769069/5000000000000000 : ℝ)^4891 := by
      have hnat : (25000023350929107243 : ℕ)^1024*5000000000000000^4891 ≤ 5000000977769069^4891*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000023350929107243 25000000000000000000 5000000977769069 5000000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000977769069/5000000000000000 : ℝ)) (X := (25000023350929107243/25000000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50049412859240511177/50000000000000000000 : ℝ) ≤ (625129265517791/625000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (50049412859240511177/50000000000000000000 : ℝ)^1024 ≤ (625129265517791/625000000000000 : ℝ)^4891 := by
      have hnat : (50049412859240511177 : ℕ)^1024*625000000000000^4891 ≤ 625129265517791^4891*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50049412859240511177 50000000000000000000 625129265517791 625000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625129265517791/625000000000000 : ℝ)) (X := (50049412859240511177/50000000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12524694754155701967/12500000000000000000 : ℝ) ≤ (5002067270515587/5000000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (12524694754155701967/12500000000000000000 : ℝ)^1024 ≤ (5002067270515587/5000000000000000 : ℝ)^4891 := by
      have hnat : (12524694754155701967 : ℕ)^1024*5000000000000000^4891 ≤ 5002067270515587^4891*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12524694754155701967 12500000000000000000 5002067270515587 5000000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002067270515587/5000000000000000 : ℝ)) (X := (12524694754155701967/12500000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23350929107243/50000000000000000000 : ℝ) ≤ ((23445062743794851429/23447500000000000000 : ℝ)+2*(1033146373259/937900000000000 : ℝ)*(4727/100000 : ℝ))^(4891/1024 : ℝ) := by
    rw [show (23445062743794851429/23447500000000000000 : ℝ)+2*(1033146373259/937900000000000 : ℝ)*(4727/100000 : ℝ)=(5000000977769069/5000000000000000 : ℝ) by norm_num, show 1+2*(23350929107243/50000000000000000000 : ℝ)=(25000023350929107243/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24694754155701967/25000000000000000000 : ℝ)+(23350929107243/50000000000000000000 : ℝ) ≤ ((23445062743794851429/23447500000000000000 : ℝ)+(1033146373259/937900000000000 : ℝ)*((4697/20000 : ℝ)+(4727/100000 : ℝ)))^(4891/1024 : ℝ) := by
    rw [show (23445062743794851429/23447500000000000000 : ℝ)+(1033146373259/937900000000000 : ℝ)*((4697/20000 : ℝ)+(4727/100000 : ℝ))=(625129265517791/625000000000000 : ℝ) by norm_num, show 1+(24694754155701967/25000000000000000000 : ℝ)+(23350929107243/50000000000000000000 : ℝ)=(50049412859240511177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24694754155701967/25000000000000000000 : ℝ) ≤ ((23445062743794851429/23447500000000000000 : ℝ)+2*(1033146373259/937900000000000 : ℝ)*(4697/20000 : ℝ))^(4891/1024 : ℝ) := by
    rw [show (23445062743794851429/23447500000000000000 : ℝ)+2*(1033146373259/937900000000000 : ℝ)*(4697/20000 : ℝ)=(5002067270515587/5000000000000000 : ℝ) by norm_num, show 1+2*(24694754155701967/25000000000000000000 : ℝ)=(12524694754155701967/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23445062743794851429/23447500000000000000 : ℝ)*(X 1 0+X 2 0)+(1033146373259/937900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (4727/100000 : ℝ)) (hi := (4697/20000 : ℝ)) (c := (23445062743794851429/23447500000000000000 : ℝ)) (alpha := (1033146373259/937900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23445062743794851429/23447500000000000000 : ℝ)*(X 0 1+X 2 1)+(1033146373259/937900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (4727/100000 : ℝ)) (hi := (4697/20000 : ℝ)) (c := (23445062743794851429/23447500000000000000 : ℝ)) (alpha := (1033146373259/937900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23445062743794851429/23447500000000000000 : ℝ)*(X 0 2+X 1 2)+(1033146373259/937900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (4727/100000 : ℝ)) (hi := (4697/20000 : ℝ)) (c := (23445062743794851429/23447500000000000000 : ℝ)) (alpha := (1033146373259/937900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-20145271/125000000 : ℝ)*X 0 0+(1100170121/2000000000 : ℝ)*X 0 1+(5138996141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340569007/2500000000 : ℝ)*X 1 0+(-1799893751/10000000000 : ℝ)*X 1 1+(2569497979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072455431/2000000000 : ℝ)*X 2 0+(2569497337/5000000000 : ℝ)*X 2 1+(-899946971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2088735997/5000000000 : ℝ)*X 0 0+(3731758721/10000000000 : ℝ)*X 0 1+(2330448007/5000000000 : ℝ)*X 0 2+(2088735997/5000000000 : ℝ)*X 1 0+(3731758721/10000000000 : ℝ)*X 1 1+(2330448007/5000000000 : ℝ)*X 1 2+(2088735997/5000000000 : ℝ)*X 2 0+(3731758721/10000000000 : ℝ)*X 2 1+(2330448007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1611786741/10000000000 : ℝ)*X 0 0+(2571351379/5000000000 : ℝ)*X 0 1+(5497090131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210623461/400000000 : ℝ)*X 1 0+(-1441799089/10000000000 : ℝ)*X 1 1+(1099418027/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1316396591/2500000000 : ℝ)*X 2 0+(1374272593/2500000000 : ℝ)*X 2 1+(-22528109/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1044473069/2500000000 : ℝ)*X 0 0+(465137721/1000000000 : ℝ)*X 0 1+(374141509/1000000000 : ℝ)*X 0 2+(1044473069/2500000000 : ℝ)*X 1 0+(465137721/1000000000 : ℝ)*X 1 1+(374141509/1000000000 : ℝ)*X 1 2+(1044473069/2500000000 : ℝ)*X 2 0+(465137721/1000000000 : ℝ)*X 2 1+(374141509/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2944014925357091490914200821/293093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (330467513/50000000000000 : ℝ)*(base1) + (1051204367/100000000000000 : ℝ)*(base19) + (326404561/20000000000000 : ℝ)*(base23) + (21015671/20000000000000 : ℝ)*(upper3) + (77966259/100000000000000 : ℝ)*(upper5) + (959952579014917/50000000000000 : ℝ)*(major0) + (959952579014917/50000000000000 : ℝ)*(major1) + (959952579014917/50000000000000 : ℝ)*(major2) + (2763541149317639/100000000000000 : ℝ)*(sp0) + (690884968801137/25000000000000 : ℝ)*(sp1) + (276353929438611/10000000000000 : ℝ)*(sp2) + (269066841453739/25000000000000 : ℝ)*(sp3) + (219013151/50000000000000 : ℝ)*(sp4) + (64255009/6250000000000 : ℝ)*(sp7) + (538134527415063/50000000000000 : ℝ)*(f.failure) + (552708185281783/20000000000000 : ℝ)*(f.sum) + (2138874070973/1465468750000000000000000000 : ℝ)*base65 + (1976260866851783607/1172375000000000000000000000000000 : ℝ)*base68 + (8231370291815466393/1172375000000000000000000000000000 : ℝ)*base69 + (280826756251341393/1172375000000000000000000000000000 : ℝ)*base71 + (11310606079823/23447500000000000000000000000 : ℝ)*base73 + (4540311358138341393/1172375000000000000000000000000000 : ℝ)*base75 + (2548971773679591393/1172375000000000000000000000000000 : ℝ)*base77 + (2493634972599341393/1172375000000000000000000000000000 : ℝ)*base79 + (166377300058513/23447500000000000000000000000 : ℝ)*base81 + (26149877/2500000000000000000000 : ℝ)*base90 + (26149877/2500000000000000000000 : ℝ)*base92 + (26149877/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1104561587465477646617191947/234475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (962321633/100000000000000 : ℝ)*(base19) + (475809373/50000000000000 : ℝ)*(base23) + (14409981/50000000000000 : ℝ)*(upper2) + (14700399/12500000000000 : ℝ)*(upper3) + (123284493/100000000000000 : ℝ)*(upper5) + (392071734797727/20000000000000 : ℝ)*(major0) + (392071734797727/20000000000000 : ℝ)*(major1) + (392071734797727/20000000000000 : ℝ)*(major2) + (8848238679/100000000000000 : ℝ)*(sp1) + (4991582397/50000000000000 : ℝ)*(sp2) + (1410885261244037/50000000000000 : ℝ)*(sp4) + (1410880355963881/50000000000000 : ℝ)*(sp5) + (1410879793852267/50000000000000 : ℝ)*(sp6) + (549473334231493/50000000000000 : ℝ)*(sp7) + (549473334231493/50000000000000 : ℝ)*(f.failure) + (1410885261244037/50000000000000 : ℝ)*(f.sum) + (8064748439767/1875800000000000000000000000 : ℝ)*base65 + (2703500098541173117/468950000000000000000000000000000 : ℝ)*base68 + (5256979406835073117/468950000000000000000000000000000 : ℝ)*base70 + (2686680290462873117/468950000000000000000000000000000 : ℝ)*base72 + (8731327345833/4689500000000000000000000000 : ℝ)*base73 + (85628431954173117/468950000000000000000000000000000 : ℝ)*base76 + (1267244321489673117/468950000000000000000000000000000 : ℝ)*base78 + (2835062010183573117/468950000000000000000000000000000 : ℝ)*base80 + (24479091837139/9379000000000000000000000000 : ℝ)*base82 + (6413153/2500000000000000000000 : ℝ)*base89 + (6413153/2500000000000000000000 : ℝ)*base91 + (6413153/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1644_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4697/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4837/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17359/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1644_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1644_s2_0 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-162151001/1000000000 : ℝ)*x 0 + (5453255061/10000000000 : ℝ)*x 1 + (5180075203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162151001/1000000000 : ℝ)^4895 ≤ (1252647268999/12500000000000 : ℝ)^3871 := by
    have hnat : (162151001 : ℕ)^4895*12500000000000^3871 ≤ 1252647268999^3871*1000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162151001 1000000000 1252647268999 12500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453255061/10000000000 : ℝ)^4895 ≤ (185803147577/400000000000 : ℝ)^3871 := by
    have hnat : (5453255061 : ℕ)^4895*400000000000^3871 ≤ 185803147577^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453255061 10000000000 185803147577 400000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180075203/10000000000 : ℝ)^4895 ≤ (2176401746923/5000000000000 : ℝ)^3871 := by
    have hnat : (5180075203 : ℕ)^4895*5000000000000^3871 ≤ 2176401746923^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180075203 10000000000 2176401746923 5000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-162151001/1000000000 : ℝ), (5453255061/10000000000 : ℝ), (5180075203/10000000000 : ℝ)] ![(1252647268999/12500000000000 : ℝ), (185803147577/400000000000 : ℝ), (2176401746923/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-162151001/1000000000 : ℝ)|^4895 ≤ (1252647268999/12500000000000 : ℝ)^3871
        have hw : |(-162151001/1000000000 : ℝ)|=(162151001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453255061/10000000000 : ℝ)|^4895 ≤ (185803147577/400000000000 : ℝ)^3871
        have hw : |(5453255061/10000000000 : ℝ)|=(5453255061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180075203/10000000000 : ℝ)|^4895 ≤ (2176401746923/5000000000000 : ℝ)^3871
        have hw : |(5180075203/10000000000 : ℝ)|=(5180075203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s2_1 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10699409/20000000 : ℝ)*x 0 + (-1762287427/10000000000 : ℝ)*x 1 + (518007589/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10699409/20000000 : ℝ)^4895 ≤ (45338230628287/100000000000000 : ℝ)^3871 := by
    have hnat : (10699409 : ℕ)^4895*100000000000000^3871 ≤ 45338230628287^3871*20000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10699409 20000000 45338230628287 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1762287427/10000000000 : ℝ)^4895 ≤ (11133727109341/100000000000000 : ℝ)^3871 := by
    have hnat : (1762287427 : ℕ)^4895*100000000000000^3871 ≤ 11133727109341^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762287427 10000000000 11133727109341 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518007589/1000000000 : ℝ)^4895 ≤ (43528042238399/100000000000000 : ℝ)^3871 := by
    have hnat : (518007589 : ℕ)^4895*100000000000000^3871 ≤ 43528042238399^3871*1000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518007589 1000000000 43528042238399 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10699409/20000000 : ℝ), (-1762287427/10000000000 : ℝ), (518007589/1000000000 : ℝ)] ![(45338230628287/100000000000000 : ℝ), (11133727109341/100000000000000 : ℝ), (43528042238399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10699409/20000000 : ℝ)|^4895 ≤ (45338230628287/100000000000000 : ℝ)^3871
        have hw : |(10699409/20000000 : ℝ)|=(10699409/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1762287427/10000000000 : ℝ)|^4895 ≤ (11133727109341/100000000000000 : ℝ)^3871
        have hw : |(-1762287427/10000000000 : ℝ)|=(1762287427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518007589/1000000000 : ℝ)|^4895 ≤ (43528042238399/100000000000000 : ℝ)^3871
        have hw : |(518007589/1000000000 : ℝ)|=(518007589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s2_2 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334356659/625000000 : ℝ)*x 0 + (5180074499/10000000000 : ℝ)*x 1 + (-220285817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334356659/625000000 : ℝ)^4895 ≤ (22669126266693/50000000000000 : ℝ)^3871 := by
    have hnat : (334356659 : ℕ)^4895*50000000000000^3871 ≤ 22669126266693^3871*625000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334356659 625000000 22669126266693 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180074499/10000000000 : ℝ)^4895 ≤ (43528027457881/100000000000000 : ℝ)^3871 := by
    have hnat : (5180074499 : ℕ)^4895*100000000000000^3871 ≤ 43528027457881^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180074499 10000000000 43528027457881 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220285817/1250000000 : ℝ)^4895 ≤ (11133719991127/100000000000000 : ℝ)^3871 := by
    have hnat : (220285817 : ℕ)^4895*100000000000000^3871 ≤ 11133719991127^3871*1250000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220285817 1250000000 11133719991127 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334356659/625000000 : ℝ), (5180074499/10000000000 : ℝ), (-220285817/1250000000 : ℝ)] ![(22669126266693/50000000000000 : ℝ), (43528027457881/100000000000000 : ℝ), (11133719991127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334356659/625000000 : ℝ)|^4895 ≤ (22669126266693/50000000000000 : ℝ)^3871
        have hw : |(334356659/625000000 : ℝ)|=(334356659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180074499/10000000000 : ℝ)|^4895 ≤ (43528027457881/100000000000000 : ℝ)^3871
        have hw : |(5180074499/10000000000 : ℝ)|=(5180074499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220285817/1250000000 : ℝ)|^4895 ≤ (11133719991127/100000000000000 : ℝ)^3871
        have hw : |(-220285817/1250000000 : ℝ)|=(220285817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s2_3 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184831083/10000000000 : ℝ)*x 0 + (3844859543/10000000000 : ℝ)*x 1 + (1136576309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184831083/10000000000 : ℝ)^4895 ≤ (33235328003493/100000000000000 : ℝ)^3871 := by
    have hnat : (4184831083 : ℕ)^4895*100000000000000^3871 ≤ 33235328003493^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184831083 10000000000 33235328003493 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3844859543/10000000000 : ℝ)^4895 ≤ (29858531445841/100000000000000 : ℝ)^3871 := by
    have hnat : (3844859543 : ℕ)^4895*100000000000000^3871 ≤ 29858531445841^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3844859543 10000000000 29858531445841 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136576309/2500000000 : ℝ)^4895 ≤ (18453070265891/50000000000000 : ℝ)^3871 := by
    have hnat : (1136576309 : ℕ)^4895*50000000000000^3871 ≤ 18453070265891^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136576309 2500000000 18453070265891 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184831083/10000000000 : ℝ), (3844859543/10000000000 : ℝ), (1136576309/2500000000 : ℝ)] ![(33235328003493/100000000000000 : ℝ), (29858531445841/100000000000000 : ℝ), (18453070265891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184831083/10000000000 : ℝ)|^4895 ≤ (33235328003493/100000000000000 : ℝ)^3871
        have hw : |(4184831083/10000000000 : ℝ)|=(4184831083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3844859543/10000000000 : ℝ)|^4895 ≤ (29858531445841/100000000000000 : ℝ)^3871
        have hw : |(3844859543/10000000000 : ℝ)|=(3844859543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136576309/2500000000 : ℝ)|^4895 ≤ (18453070265891/50000000000000 : ℝ)^3871
        have hw : |(1136576309/2500000000 : ℝ)|=(1136576309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s2_4 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1621579569/10000000000 : ℝ)*x 0 + (5182194017/10000000000 : ℝ)*x 1 + (1090222833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1621579569/10000000000 : ℝ)^4895 ≤ (400868870331/4000000000000 : ℝ)^3871 := by
    have hnat : (1621579569 : ℕ)^4895*4000000000000^3871 ≤ 400868870331^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621579569 10000000000 400868870331 4000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182194017/10000000000 : ℝ)^4895 ≤ (43550550296011/100000000000000 : ℝ)^3871 := by
    have hnat : (5182194017 : ℕ)^4895*100000000000000^3871 ≤ 43550550296011^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182194017 10000000000 43550550296011 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090222833/2000000000 : ℝ)^4895 ≤ (46427727929471/100000000000000 : ℝ)^3871 := by
    have hnat : (1090222833 : ℕ)^4895*100000000000000^3871 ≤ 46427727929471^3871*2000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090222833 2000000000 46427727929471 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1621579569/10000000000 : ℝ), (5182194017/10000000000 : ℝ), (1090222833/2000000000 : ℝ)] ![(400868870331/4000000000000 : ℝ), (43550550296011/100000000000000 : ℝ), (46427727929471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1621579569/10000000000 : ℝ)|^4895 ≤ (400868870331/4000000000000 : ℝ)^3871
        have hw : |(-1621579569/10000000000 : ℝ)|=(1621579569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182194017/10000000000 : ℝ)|^4895 ≤ (43550550296011/100000000000000 : ℝ)^3871
        have hw : |(5182194017/10000000000 : ℝ)|=(5182194017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090222833/2000000000 : ℝ)|^4895 ≤ (46427727929471/100000000000000 : ℝ)^3871
        have hw : |(1090222833/2000000000 : ℝ)|=(1090222833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s2_5 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319193317/2500000000 : ℝ)*x 0 + (-1491248499/10000000000 : ℝ)*x 1 + (2725556749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319193317/2500000000 : ℝ)^4895 ≤ (696219636633/1562500000000 : ℝ)^3871 := by
    have hnat : (1319193317 : ℕ)^4895*1562500000000^3871 ≤ 696219636633^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319193317 2500000000 696219636633 1562500000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1491248499/10000000000 : ℝ)^4895 ≤ (1126777811403/12500000000000 : ℝ)^3871 := by
    have hnat : (1491248499 : ℕ)^4895*12500000000000^3871 ≤ 1126777811403^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491248499 10000000000 1126777811403 12500000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725556749/5000000000 : ℝ)^4895 ≤ (23213860372891/50000000000000 : ℝ)^3871 := by
    have hnat : (2725556749 : ℕ)^4895*50000000000000^3871 ≤ 23213860372891^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725556749 5000000000 23213860372891 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319193317/2500000000 : ℝ), (-1491248499/10000000000 : ℝ), (2725556749/5000000000 : ℝ)] ![(696219636633/1562500000000 : ℝ), (1126777811403/12500000000000 : ℝ), (23213860372891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319193317/2500000000 : ℝ)|^4895 ≤ (696219636633/1562500000000 : ℝ)^3871
        have hw : |(1319193317/2500000000 : ℝ)|=(1319193317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1491248499/10000000000 : ℝ)|^4895 ≤ (1126777811403/12500000000000 : ℝ)^3871
        have hw : |(-1491248499/10000000000 : ℝ)|=(1491248499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725556749/5000000000 : ℝ)|^4895 ≤ (23213860372891/50000000000000 : ℝ)^3871
        have hw : |(2725556749/5000000000 : ℝ)|=(2725556749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s2_6 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319193529/2500000000 : ℝ)*x 0 + (2725556537/5000000000 : ℝ)*x 1 + (-1491247913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319193529/2500000000 : ℝ)^4895 ≤ (22279032899701/50000000000000 : ℝ)^3871 := by
    have hnat : (1319193529 : ℕ)^4895*50000000000000^3871 ≤ 22279032899701^3871*2500000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319193529 2500000000 22279032899701 50000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725556537/5000000000 : ℝ)^4895 ≤ (46427716179239/100000000000000 : ℝ)^3871 := by
    have hnat : (2725556537 : ℕ)^4895*100000000000000^3871 ≤ 46427716179239^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725556537 5000000000 46427716179239 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491247913/10000000000 : ℝ)^4895 ≤ (9014218011973/100000000000000 : ℝ)^3871 := by
    have hnat : (1491247913 : ℕ)^4895*100000000000000^3871 ≤ 9014218011973^3871*10000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491247913 10000000000 9014218011973 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319193529/2500000000 : ℝ), (2725556537/5000000000 : ℝ), (-1491247913/10000000000 : ℝ)] ![(22279032899701/50000000000000 : ℝ), (46427716179239/100000000000000 : ℝ), (9014218011973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319193529/2500000000 : ℝ)|^4895 ≤ (22279032899701/50000000000000 : ℝ)^3871
        have hw : |(1319193529/2500000000 : ℝ)|=(1319193529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725556537/5000000000 : ℝ)|^4895 ≤ (46427716179239/100000000000000 : ℝ)^3871
        have hw : |(2725556537/5000000000 : ℝ)|=(2725556537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1491247913/10000000000 : ℝ)|^4895 ≤ (9014218011973/100000000000000 : ℝ)^3871
        have hw : |(-1491247913/10000000000 : ℝ)|=(1491247913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1644_s2_7 (p : ℝ) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2092506657/5000000000 : ℝ)*x 0 + (2270432251/5000000000 : ℝ)*x 1 + (1925179293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092506657/5000000000 : ℝ)^4895 ≤ (33237158109813/100000000000000 : ℝ)^3871 := by
    have hnat : (2092506657 : ℕ)^4895*100000000000000^3871 ≤ 33237158109813^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092506657 5000000000 33237158109813 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270432251/5000000000 : ℝ)^4895 ≤ (36850298875641/100000000000000 : ℝ)^3871 := by
    have hnat : (2270432251 : ℕ)^4895*100000000000000^3871 ≤ 36850298875641^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270432251 5000000000 36850298875641 100000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925179293/5000000000 : ℝ)^4895 ≤ (7478135751557/25000000000000 : ℝ)^3871 := by
    have hnat : (1925179293 : ℕ)^4895*25000000000000^3871 ≤ 7478135751557^3871*5000000000^4895 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925179293 5000000000 7478135751557 25000000000000 4895 3871 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4895/1024 : ℝ)) 4895 3871 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092506657/5000000000 : ℝ), (2270432251/5000000000 : ℝ), (1925179293/5000000000 : ℝ)] ![(33237158109813/100000000000000 : ℝ), (36850298875641/100000000000000 : ℝ), (7478135751557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092506657/5000000000 : ℝ)|^4895 ≤ (33237158109813/100000000000000 : ℝ)^3871
        have hw : |(2092506657/5000000000 : ℝ)|=(2092506657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270432251/5000000000 : ℝ)|^4895 ≤ (36850298875641/100000000000000 : ℝ)^3871
        have hw : |(2270432251/5000000000 : ℝ)|=(2270432251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1925179293/5000000000 : ℝ)|^4895 ≤ (7478135751557/25000000000000 : ℝ)^3871
        have hw : |(1925179293/5000000000 : ℝ)|=(1925179293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1644_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4837/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10561/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8183/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17359/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4837/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17359/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4837/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17359/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4837/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17359/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4837/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17359/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4837/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17359/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4837/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4837/50000 : ℝ) ^ (4891/1024 : ℝ) ≤ (1428506365269021/100000000000000000000 : ℝ) := by
    have hpowers : (4837/50000 : ℝ)^4891 ≤ (1428506365269021/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4837 : ℕ)^4891*100000000000000000000^1024 ≤ 1428506365269021^1024*50000^4891 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4837 50000 1428506365269021 100000000000000000000 4891 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4837/50000 : ℝ)) (X := (1428506365269021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17359/100000 : ℝ) ^ (4891/1024 : ℝ) ≤ (2914746290501467/12500000000000000000 : ℝ) := by
    have hpowers : (17359/100000 : ℝ)^4891 ≤ (2914746290501467/12500000000000000000 : ℝ)^1024 := by
      have hnat : (17359 : ℕ)^4891*12500000000000000000^1024 ≤ 2914746290501467^1024*100000^4891 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17359 100000 2914746290501467 12500000000000000000 4891 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17359/100000 : ℝ)) (X := (2914746290501467/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001428506365269021/50000000000000000000 : ℝ) ≤ (10000059814925257/10000000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (50001428506365269021/50000000000000000000 : ℝ)^1024 ≤ (10000059814925257/10000000000000000 : ℝ)^4891 := by
      have hnat : (50001428506365269021 : ℕ)^1024*10000000000000000^4891 ≤ 10000059814925257^4891*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001428506365269021 50000000000000000000 10000059814925257 10000000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000059814925257/10000000000000000 : ℝ)) (X := (50001428506365269021/50000000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024746476689280757/100000000000000000000 : ℝ) ≤ (5000259025899763/5000000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (100024746476689280757/100000000000000000000 : ℝ)^1024 ≤ (5000259025899763/5000000000000000 : ℝ)^4891 := by
      have hnat : (100024746476689280757 : ℕ)^1024*5000000000000000^4891 ≤ 5000259025899763^4891*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024746476689280757 100000000000000000000 5000259025899763 5000000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000259025899763/5000000000000000 : ℝ)) (X := (100024746476689280757/100000000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252914746290501467/6250000000000000000 : ℝ) ≤ (2000195257734759/2000000000000000 : ℝ) ^ (4891/1024 : ℝ) := by
    have hpowers : (6252914746290501467/6250000000000000000 : ℝ)^1024 ≤ (2000195257734759/2000000000000000 : ℝ)^4891 := by
      have hnat : (6252914746290501467 : ℕ)^1024*2000000000000000^4891 ≤ 2000195257734759^4891*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252914746290501467 6250000000000000000 2000195257734759 2000000000000000 1024 4891 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000195257734759/2000000000000000 : ℝ)) (X := (6252914746290501467/6250000000000000000 : ℝ)) (by norm_num) 4891 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1428506365269021/100000000000000000000 : ℝ) ≤ ((76841593710657243433/76850000000000000000 : ℝ)+2*(458236874269/768500000000000 : ℝ)*(4837/50000 : ℝ))^(4891/1024 : ℝ) := by
    rw [show (76841593710657243433/76850000000000000000 : ℝ)+2*(458236874269/768500000000000 : ℝ)*(4837/50000 : ℝ)=(10000059814925257/10000000000000000 : ℝ) by norm_num, show 1+2*(1428506365269021/100000000000000000000 : ℝ)=(50001428506365269021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2914746290501467/12500000000000000000 : ℝ)+(1428506365269021/100000000000000000000 : ℝ) ≤ ((76841593710657243433/76850000000000000000 : ℝ)+(458236874269/768500000000000 : ℝ)*((17359/100000 : ℝ)+(4837/50000 : ℝ)))^(4891/1024 : ℝ) := by
    rw [show (76841593710657243433/76850000000000000000 : ℝ)+(458236874269/768500000000000 : ℝ)*((17359/100000 : ℝ)+(4837/50000 : ℝ))=(5000259025899763/5000000000000000 : ℝ) by norm_num, show 1+(2914746290501467/12500000000000000000 : ℝ)+(1428506365269021/100000000000000000000 : ℝ)=(100024746476689280757/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2914746290501467/12500000000000000000 : ℝ) ≤ ((76841593710657243433/76850000000000000000 : ℝ)+2*(458236874269/768500000000000 : ℝ)*(17359/100000 : ℝ))^(4891/1024 : ℝ) := by
    rw [show (76841593710657243433/76850000000000000000 : ℝ)+2*(458236874269/768500000000000 : ℝ)*(17359/100000 : ℝ)=(2000195257734759/2000000000000000 : ℝ) by norm_num, show 1+2*(2914746290501467/12500000000000000000 : ℝ)=(6252914746290501467/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (76841593710657243433/76850000000000000000 : ℝ)*(X 1 0+X 2 0)+(458236874269/768500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (4837/50000 : ℝ)) (hi := (17359/100000 : ℝ)) (c := (76841593710657243433/76850000000000000000 : ℝ)) (alpha := (458236874269/768500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (76841593710657243433/76850000000000000000 : ℝ)*(X 0 1+X 2 1)+(458236874269/768500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (4837/50000 : ℝ)) (hi := (17359/100000 : ℝ)) (c := (76841593710657243433/76850000000000000000 : ℝ)) (alpha := (458236874269/768500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (76841593710657243433/76850000000000000000 : ℝ)*(X 0 2+X 1 2)+(458236874269/768500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4891/1024 : ℝ)) (lo := (4837/50000 : ℝ)) (hi := (17359/100000 : ℝ)) (c := (76841593710657243433/76850000000000000000 : ℝ)) (alpha := (458236874269/768500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-162151001/1000000000 : ℝ)*X 0 0+(5453255061/10000000000 : ℝ)*X 0 1+(5180075203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((10699409/20000000 : ℝ)*X 1 0+(-1762287427/10000000000 : ℝ)*X 1 1+(518007589/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334356659/625000000 : ℝ)*X 2 0+(5180074499/10000000000 : ℝ)*X 2 1+(-220285817/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4184831083/10000000000 : ℝ)*X 0 0+(3844859543/10000000000 : ℝ)*X 0 1+(1136576309/2500000000 : ℝ)*X 0 2+(4184831083/10000000000 : ℝ)*X 1 0+(3844859543/10000000000 : ℝ)*X 1 1+(1136576309/2500000000 : ℝ)*X 1 2+(4184831083/10000000000 : ℝ)*X 2 0+(3844859543/10000000000 : ℝ)*X 2 1+(1136576309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1621579569/10000000000 : ℝ)*X 0 0+(5182194017/10000000000 : ℝ)*X 0 1+(1090222833/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319193317/2500000000 : ℝ)*X 1 0+(-1491248499/10000000000 : ℝ)*X 1 1+(2725556749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319193529/2500000000 : ℝ)*X 2 0+(2725556537/5000000000 : ℝ)*X 2 1+(-1491247913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2092506657/5000000000 : ℝ)*X 0 0+(2270432251/5000000000 : ℝ)*X 0 1+(1925179293/5000000000 : ℝ)*X 0 2+(2092506657/5000000000 : ℝ)*X 1 0+(2270432251/5000000000 : ℝ)*X 1 1+(1925179293/5000000000 : ℝ)*X 1 2+(2092506657/5000000000 : ℝ)*X 2 0+(2270432251/5000000000 : ℝ)*X 2 1+(1925179293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1644_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5192070960734983780329293091/480312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229263799/20000000000000 : ℝ)*(base19) + (581087881/25000000000000 : ℝ)*(base23) + (131028429/100000000000000 : ℝ)*(upper4) + (156832679/25000000000000 : ℝ)*(upper5) + (635784480265391/25000000000000 : ℝ)*(major0) + (635784480265391/25000000000000 : ℝ)*(major1) + (635784480265391/25000000000000 : ℝ)*(major2) + (732120071735401/20000000000000 : ℝ)*(sp0) + (3660628876071827/100000000000000 : ℝ)*(sp1) + (1830314740843019/50000000000000 : ℝ)*(sp2) + (356409087514497/25000000000000 : ℝ)*(sp3) + (31447360557/100000000000000 : ℝ)*(sp4) + (89182337/5000000000000 : ℝ)*(sp5) + (7325701671/100000000000000 : ℝ)*(sp7) + (71282183787983/5000000000000 : ℝ)*(f.failure) + (3660631806037563/100000000000000 : ℝ)*(f.sum) + (121117434122841/38425000000000000000000000000 : ℝ)*base65 + (2123088815875172697/1921250000000000000000000000000000 : ℝ)*base68 + (6705444575152327303/1921250000000000000000000000000000 : ℝ)*base69 + (14370007808542327303/1921250000000000000000000000000000 : ℝ)*base71 + (102477303582509/38425000000000000000000000000 : ℝ)*base74 + (15510820302264827303/1921250000000000000000000000000000 : ℝ)*base75 + (8165206336637327303/1921250000000000000000000000000000 : ℝ)*base77 + (14667896141679827303/1921250000000000000000000000000000 : ℝ)*base79 + (33259113058083/19212500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2073443/250000000000000000000 : ℝ)*base89 + (2073443/250000000000000000000 : ℝ)*base91 + (2073443/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7473134059475221765041/600390625000000000000000000 : ℝ) := by norm_num
    linear_combination (632381091/50000000000000 : ℝ)*(base19) + (2816568597/100000000000000 : ℝ)*(base23) + (29100741/50000000000000 : ℝ)*(upper3) + (399746403/100000000000000 : ℝ)*(lower4) + (71301403/25000000000000 : ℝ)*(upper5) + (1291697482391953/50000000000000 : ℝ)*(major0) + (1291697482391953/50000000000000 : ℝ)*(major1) + (1291697482391953/50000000000000 : ℝ)*(major2) + (9928338157/100000000000000 : ℝ)*(sp1) + (2415661311/10000000000000 : ℝ)*(sp2) + (3718578364559867/100000000000000 : ℝ)*(sp4) + (464820896432441/12500000000000 : ℝ)*(sp5) + (46481892392227/1250000000000 : ℝ)*(sp6) + (289642230020789/20000000000000 : ℝ)*(sp7) + (289642230020789/20000000000000 : ℝ)*(f.failure) + (3718578364559867/100000000000000 : ℝ)*(f.sum) + (34571197525739/38425000000000000000000000000 : ℝ)*base65 + (3270515434294494649/3842500000000000000000000000000000 : ℝ)*base67 + (1940004867414494649/3842500000000000000000000000000000 : ℝ)*base69 + (18882463857918005351/3842500000000000000000000000000000 : ℝ)*base72 + (138257468364139/38425000000000000000000000000 : ℝ)*base73 + (10701926258593005351/3842500000000000000000000000000000 : ℝ)*base76 + (18037092324548005351/3842500000000000000000000000000000 : ℝ)*base78 + (24141323193876994649/3842500000000000000000000000000000 : ℝ)*base79 + (1857823993863/300195312500000000000000000 : ℝ)*base81 + (4602031/1000000000000000000000 : ℝ)*base90 + (4602031/1000000000000000000000 : ℝ)*base92 + (4602031/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1644_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4837/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10561/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1644_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1644_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10561/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1644_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1644_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1644_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4891/1024 : ℝ) ≤ p) (hpb : p ≤ (4895/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89192621/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10561/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1644_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
