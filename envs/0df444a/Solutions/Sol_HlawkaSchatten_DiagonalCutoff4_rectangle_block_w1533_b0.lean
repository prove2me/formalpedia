-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1533_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:33.154211+00:00
-- url     : https://prove2.me/submissions/7ecc4f98-5a84-4a18-8988-8a7dbc691633

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
theorem support_rectangle_w1533_s0_0 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-831893073/5000000000 : ℝ)*x 0 + (5896841923/10000000000 : ℝ)*x 1 + (1216049431/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (831893073/5000000000 : ℝ)^4563 ≤ (9902028916979/100000000000000 : ℝ)^3539 := by
    have hnat : (831893073 : ℕ)^4563*100000000000000^3539 ≤ 9902028916979^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831893073 5000000000 9902028916979 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5896841923/10000000000 : ℝ)^4563 ≤ (506114592741/1000000000000 : ℝ)^3539 := by
    have hnat : (5896841923 : ℕ)^4563*1000000000000^3539 ≤ 506114592741^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5896841923 10000000000 506114592741 1000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216049431/2500000000 : ℝ)^4563 ≤ (39486511792601/100000000000000 : ℝ)^3539 := by
    have hnat : (1216049431 : ℕ)^4563*100000000000000^3539 ≤ 39486511792601^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216049431 2500000000 39486511792601 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-831893073/5000000000 : ℝ), (5896841923/10000000000 : ℝ), (1216049431/2500000000 : ℝ)] ![(9902028916979/100000000000000 : ℝ), (506114592741/1000000000000 : ℝ), (39486511792601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-831893073/5000000000 : ℝ)|^4563 ≤ (9902028916979/100000000000000 : ℝ)^3539
        have hw : |(-831893073/5000000000 : ℝ)|=(831893073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5896841923/10000000000 : ℝ)|^4563 ≤ (506114592741/1000000000000 : ℝ)^3539
        have hw : |(5896841923/10000000000 : ℝ)|=(5896841923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1216049431/2500000000 : ℝ)|^4563 ≤ (39486511792601/100000000000000 : ℝ)^3539
        have hw : |(1216049431/2500000000 : ℝ)|=(1216049431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s0_1 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2736712553/5000000000 : ℝ)*x 0 + (-2241057423/10000000000 : ℝ)*x 1 + (972839553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2736712553/5000000000 : ℝ)^4563 ≤ (45975365162169/100000000000000 : ℝ)^3539 := by
    have hnat : (2736712553 : ℕ)^4563*100000000000000^3539 ≤ 45975365162169^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736712553 5000000000 45975365162169 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241057423/10000000000 : ℝ)^4563 ≤ (1453812260043/10000000000000 : ℝ)^3539 := by
    have hnat : (2241057423 : ℕ)^4563*10000000000000^3539 ≤ 1453812260043^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241057423 10000000000 1453812260043 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (972839553/2000000000 : ℝ)^4563 ≤ (19743256110867/50000000000000 : ℝ)^3539 := by
    have hnat : (972839553 : ℕ)^4563*50000000000000^3539 ≤ 19743256110867^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972839553 2000000000 19743256110867 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2736712553/5000000000 : ℝ), (-2241057423/10000000000 : ℝ), (972839553/2000000000 : ℝ)] ![(45975365162169/100000000000000 : ℝ), (1453812260043/10000000000000 : ℝ), (19743256110867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2736712553/5000000000 : ℝ)|^4563 ≤ (45975365162169/100000000000000 : ℝ)^3539
        have hw : |(2736712553/5000000000 : ℝ)|=(2736712553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2241057423/10000000000 : ℝ)|^4563 ≤ (1453812260043/10000000000000 : ℝ)^3539
        have hw : |(-2241057423/10000000000 : ℝ)|=(2241057423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(972839553/2000000000 : ℝ)|^4563 ≤ (19743256110867/50000000000000 : ℝ)^3539
        have hw : |(972839553/2000000000 : ℝ)|=(972839553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s0_2 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5473425069/10000000000 : ℝ)*x 0 + (1216049437/2500000000 : ℝ)*x 1 + (-560264373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5473425069/10000000000 : ℝ)^4563 ≤ (11493841190363/25000000000000 : ℝ)^3539 := by
    have hnat : (5473425069 : ℕ)^4563*25000000000000^3539 ≤ 11493841190363^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473425069 10000000000 11493841190363 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1216049437/2500000000 : ℝ)^4563 ≤ (39486512043801/100000000000000 : ℝ)^3539 := by
    have hnat : (1216049437 : ℕ)^4563*100000000000000^3539 ≤ 39486512043801^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216049437 2500000000 39486512043801 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560264373/2500000000 : ℝ)^4563 ≤ (14538123177561/100000000000000 : ℝ)^3539 := by
    have hnat : (560264373 : ℕ)^4563*100000000000000^3539 ≤ 14538123177561^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560264373 2500000000 14538123177561 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5473425069/10000000000 : ℝ), (1216049437/2500000000 : ℝ), (-560264373/2500000000 : ℝ)] ![(11493841190363/25000000000000 : ℝ), (39486512043801/100000000000000 : ℝ), (14538123177561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5473425069/10000000000 : ℝ)|^4563 ≤ (11493841190363/25000000000000 : ℝ)^3539
        have hw : |(5473425069/10000000000 : ℝ)|=(5473425069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1216049437/2500000000 : ℝ)|^4563 ≤ (39486512043801/100000000000000 : ℝ)^3539
        have hw : |(1216049437/2500000000 : ℝ)|=(1216049437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560264373/2500000000 : ℝ)|^4563 ≤ (14538123177561/100000000000000 : ℝ)^3539
        have hw : |(-560264373/2500000000 : ℝ)|=(560264373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s0_3 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2069764119/5000000000 : ℝ)*x 0 + (3091633107/10000000000 : ℝ)*x 1 + (546793353/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069764119/5000000000 : ℝ)^4563 ≤ (32071304283987/100000000000000 : ℝ)^3539 := by
    have hnat : (2069764119 : ℕ)^4563*100000000000000^3539 ≤ 32071304283987^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069764119 5000000000 32071304283987 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091633107/10000000000 : ℝ)^4563 ≤ (22012796696823/100000000000000 : ℝ)^3539 := by
    have hnat : (3091633107 : ℕ)^4563*100000000000000^3539 ≤ 22012796696823^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091633107 10000000000 22012796696823 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546793353/1000000000 : ℝ)^4563 ≤ (11478974751981/25000000000000 : ℝ)^3539 := by
    have hnat : (546793353 : ℕ)^4563*25000000000000^3539 ≤ 11478974751981^3539*1000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546793353 1000000000 11478974751981 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069764119/5000000000 : ℝ), (3091633107/10000000000 : ℝ), (546793353/1000000000 : ℝ)] ![(32071304283987/100000000000000 : ℝ), (22012796696823/100000000000000 : ℝ), (11478974751981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069764119/5000000000 : ℝ)|^4563 ≤ (32071304283987/100000000000000 : ℝ)^3539
        have hw : |(2069764119/5000000000 : ℝ)|=(2069764119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091633107/10000000000 : ℝ)|^4563 ≤ (22012796696823/100000000000000 : ℝ)^3539
        have hw : |(3091633107/10000000000 : ℝ)|=(3091633107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546793353/1000000000 : ℝ)|^4563 ≤ (11478974751981/25000000000000 : ℝ)^3539
        have hw : |(546793353/1000000000 : ℝ)|=(546793353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s0_4 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1667131283/10000000000 : ℝ)*x 0 + (611303639/1250000000 : ℝ)*x 1 + (2934837023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1667131283/10000000000 : ℝ)^4563 ≤ (2481926367907/25000000000000 : ℝ)^3539 := by
    have hnat : (1667131283 : ℕ)^4563*25000000000000^3539 ≤ 2481926367907^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667131283 10000000000 2481926367907 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611303639/1250000000 : ℝ)^4563 ≤ (19880640162899/50000000000000 : ℝ)^3539 := by
    have hnat : (611303639 : ℕ)^4563*50000000000000^3539 ≤ 19880640162899^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611303639 1250000000 19880640162899 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934837023/5000000000 : ℝ)^4563 ≤ (50311014195411/100000000000000 : ℝ)^3539 := by
    have hnat : (2934837023 : ℕ)^4563*100000000000000^3539 ≤ 50311014195411^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934837023 5000000000 50311014195411 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1667131283/10000000000 : ℝ), (611303639/1250000000 : ℝ), (2934837023/5000000000 : ℝ)] ![(2481926367907/25000000000000 : ℝ), (19880640162899/50000000000000 : ℝ), (50311014195411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1667131283/10000000000 : ℝ)|^4563 ≤ (2481926367907/25000000000000 : ℝ)^3539
        have hw : |(-1667131283/10000000000 : ℝ)|=(1667131283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(611303639/1250000000 : ℝ)|^4563 ≤ (19880640162899/50000000000000 : ℝ)^3539
        have hw : |(611303639/1250000000 : ℝ)|=(611303639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2934837023/5000000000 : ℝ)|^4563 ≤ (50311014195411/100000000000000 : ℝ)^3539
        have hw : |(2934837023/5000000000 : ℝ)|=(2934837023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s0_5 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2595606799/5000000000 : ℝ)*x 0 + (-1235581351/10000000000 : ℝ)*x 1 + (5869674119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2595606799/5000000000 : ℝ)^4563 ≤ (1073551145509/2500000000000 : ℝ)^3539 := by
    have hnat : (2595606799 : ℕ)^4563*2500000000000^3539 ≤ 1073551145509^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595606799 5000000000 1073551145509 2500000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1235581351/10000000000 : ℝ)^4563 ≤ (6746939169863/100000000000000 : ℝ)^3539 := by
    have hnat : (1235581351 : ℕ)^4563*100000000000000^3539 ≤ 6746939169863^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235581351 10000000000 6746939169863 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5869674119/10000000000 : ℝ)^4563 ≤ (50311015002167/100000000000000 : ℝ)^3539 := by
    have hnat : (5869674119 : ℕ)^4563*100000000000000^3539 ≤ 50311015002167^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5869674119 10000000000 50311015002167 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2595606799/5000000000 : ℝ), (-1235581351/10000000000 : ℝ), (5869674119/10000000000 : ℝ)] ![(1073551145509/2500000000000 : ℝ), (6746939169863/100000000000000 : ℝ), (50311015002167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2595606799/5000000000 : ℝ)|^4563 ≤ (1073551145509/2500000000000 : ℝ)^3539
        have hw : |(2595606799/5000000000 : ℝ)|=(2595606799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1235581351/10000000000 : ℝ)|^4563 ≤ (6746939169863/100000000000000 : ℝ)^3539
        have hw : |(-1235581351/10000000000 : ℝ)|=(1235581351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5869674119/10000000000 : ℝ)|^4563 ≤ (50311015002167/100000000000000 : ℝ)^3539
        have hw : |(5869674119/10000000000 : ℝ)|=(5869674119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s0_6 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191213559/10000000000 : ℝ)*x 0 + (1173934879/2000000000 : ℝ)*x 1 + (-1235580977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191213559/10000000000 : ℝ)^4563 ≤ (42942045404403/100000000000000 : ℝ)^3539 := by
    have hnat : (5191213559 : ℕ)^4563*100000000000000^3539 ≤ 42942045404403^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191213559 10000000000 42942045404403 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1173934879/2000000000 : ℝ)^4563 ≤ (10062203610473/20000000000000 : ℝ)^3539 := by
    have hnat : (1173934879 : ℕ)^4563*20000000000000^3539 ≤ 10062203610473^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173934879 2000000000 10062203610473 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1235580977/10000000000 : ℝ)^4563 ≤ (1349387307341/20000000000000 : ℝ)^3539 := by
    have hnat : (1235580977 : ℕ)^4563*20000000000000^3539 ≤ 1349387307341^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235580977 10000000000 1349387307341 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191213559/10000000000 : ℝ), (1173934879/2000000000 : ℝ), (-1235580977/10000000000 : ℝ)] ![(42942045404403/100000000000000 : ℝ), (10062203610473/20000000000000 : ℝ), (1349387307341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191213559/10000000000 : ℝ)|^4563 ≤ (42942045404403/100000000000000 : ℝ)^3539
        have hw : |(5191213559/10000000000 : ℝ)|=(5191213559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1173934879/2000000000 : ℝ)|^4563 ≤ (10062203610473/20000000000000 : ℝ)^3539
        have hw : |(1173934879/2000000000 : ℝ)|=(1173934879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1235580977/10000000000 : ℝ)|^4563 ≤ (1349387307341/20000000000000 : ℝ)^3539
        have hw : |(-1235580977/10000000000 : ℝ)|=(1235580977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s0_7 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207361247/500000000 : ℝ)*x 0 + (5407570311/10000000000 : ℝ)*x 1 + (78853771/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207361247/500000000 : ℝ)^4563 ≤ (6429641946401/20000000000000 : ℝ)^3539 := by
    have hnat : (207361247 : ℕ)^4563*20000000000000^3539 ≤ 6429641946401^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207361247 500000000 6429641946401 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407570311/10000000000 : ℝ)^4563 ≤ (45263390526467/100000000000000 : ℝ)^3539 := by
    have hnat : (5407570311 : ℕ)^4563*100000000000000^3539 ≤ 45263390526467^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407570311 10000000000 45263390526467 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78853771/250000000 : ℝ)^4563 ≤ (705887491457/3125000000000 : ℝ)^3539 := by
    have hnat : (78853771 : ℕ)^4563*3125000000000^3539 ≤ 705887491457^3539*250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78853771 250000000 705887491457 3125000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207361247/500000000 : ℝ), (5407570311/10000000000 : ℝ), (78853771/250000000 : ℝ)] ![(6429641946401/20000000000000 : ℝ), (45263390526467/100000000000000 : ℝ), (705887491457/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207361247/500000000 : ℝ)|^4563 ≤ (6429641946401/20000000000000 : ℝ)^3539
        have hw : |(207361247/500000000 : ℝ)|=(207361247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407570311/10000000000 : ℝ)|^4563 ≤ (45263390526467/100000000000000 : ℝ)^3539
        have hw : |(5407570311/10000000000 : ℝ)|=(5407570311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(78853771/250000000 : ℝ)|^4563 ≤ (705887491457/3125000000000 : ℝ)^3539
        have hw : |(78853771/250000000 : ℝ)|=(78853771/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1533_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1547/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5043/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4561/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4561 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4561*1^1024 ≤ 0^1024*1^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4561/1024 : ℝ) ≤ (844315553998189867/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4561 ≤ (844315553998189867/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4561*50000000000000000000^1024 ≤ 844315553998189867^1024*5^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 844315553998189867 50000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (844315553998189867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4561 := by
      have hnat : (1 : ℕ)^1024*1^4561 ≤ 1^4561*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50844315553998189867/50000000000000000000 : ℝ) ≤ (5018833022563377/5000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50844315553998189867/50000000000000000000 : ℝ)^1024 ≤ (5018833022563377/5000000000000000 : ℝ)^4561 := by
      have hnat : (50844315553998189867 : ℕ)^1024*5000000000000000^4561 ≤ 5018833022563377^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50844315553998189867 50000000000000000000 5018833022563377 5000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5018833022563377/5000000000000000 : ℝ)) (X := (50844315553998189867/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25844315553998189867/25000000000000000000 : ℝ) ≤ (2518833022563377/2500000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (25844315553998189867/25000000000000000000 : ℝ)^1024 ≤ (2518833022563377/2500000000000000 : ℝ)^4561 := by
      have hnat : (25844315553998189867 : ℕ)^1024*2500000000000000^4561 ≤ 2518833022563377^4561*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25844315553998189867 25000000000000000000 2518833022563377 2500000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2518833022563377/2500000000000000 : ℝ)) (X := (25844315553998189867/25000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(18833022563377/2000000000000000 : ℝ)*(0 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18833022563377/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(844315553998189867/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(18833022563377/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4561/1024 : ℝ) := by
    rw [show (1 : ℝ)+(18833022563377/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5018833022563377/5000000000000000 : ℝ) by norm_num, show 1+(844315553998189867/50000000000000000000 : ℝ)+(0 : ℝ)=(50844315553998189867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(844315553998189867/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(18833022563377/2000000000000000 : ℝ)*(2/5 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18833022563377/2000000000000000 : ℝ)*(2/5 : ℝ)=(2518833022563377/2500000000000000 : ℝ) by norm_num, show 1+2*(844315553998189867/50000000000000000000 : ℝ)=(25844315553998189867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(18833022563377/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18833022563377/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(18833022563377/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18833022563377/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(18833022563377/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18833022563377/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-831893073/5000000000 : ℝ)*X 0 0+(5896841923/10000000000 : ℝ)*X 0 1+(1216049431/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2736712553/5000000000 : ℝ)*X 1 0+(-2241057423/10000000000 : ℝ)*X 1 1+(972839553/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5473425069/10000000000 : ℝ)*X 2 0+(1216049437/2500000000 : ℝ)*X 2 1+(-560264373/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2069764119/5000000000 : ℝ)*X 0 0+(3091633107/10000000000 : ℝ)*X 0 1+(546793353/1000000000 : ℝ)*X 0 2+(2069764119/5000000000 : ℝ)*X 1 0+(3091633107/10000000000 : ℝ)*X 1 1+(546793353/1000000000 : ℝ)*X 1 2+(2069764119/5000000000 : ℝ)*X 2 0+(3091633107/10000000000 : ℝ)*X 2 1+(546793353/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1667131283/10000000000 : ℝ)*X 0 0+(611303639/1250000000 : ℝ)*X 0 1+(2934837023/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2595606799/5000000000 : ℝ)*X 1 0+(-1235581351/10000000000 : ℝ)*X 1 1+(5869674119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5191213559/10000000000 : ℝ)*X 2 0+(1173934879/2000000000 : ℝ)*X 2 1+(-1235580977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((207361247/500000000 : ℝ)*X 0 0+(5407570311/10000000000 : ℝ)*X 0 1+(78853771/250000000 : ℝ)*X 0 2+(207361247/500000000 : ℝ)*X 1 0+(5407570311/10000000000 : ℝ)*X 1 1+(78853771/250000000 : ℝ)*X 1 2+(207361247/500000000 : ℝ)*X 2 0+(5407570311/10000000000 : ℝ)*X 2 1+(78853771/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22401217952362577896413/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50784961/100000000000000 : ℝ)*(base1) + (934654431/100000000000000 : ℝ)*(base19) + (185621631/20000000000000 : ℝ)*(base23) + (5219303/4000000000000 : ℝ)*(upper3) + (108553777/100000000000000 : ℝ)*(upper5) + (69460972603577/10000000000000 : ℝ)*(major0) + (69460972603577/10000000000000 : ℝ)*(major1) + (69460972603577/10000000000000 : ℝ)*(major2) + (193678204447103/20000000000000 : ℝ)*(sp0) + (60524581683651/6250000000000 : ℝ)*(sp1) + (968393313484693/100000000000000 : ℝ)*(sp2) + (420823544192873/100000000000000 : ℝ)*(sp3) + (3270142293/100000000000000 : ℝ)*(sp4) + (1466159401/100000000000000 : ℝ)*(sp7) + (210412530568617/50000000000000 : ℝ)*(f.failure) + (60524640099553/6250000000000 : ℝ)*(f.sum) + (4884636650471/10000000000000000000000000000 : ℝ)*base66 + (39231793739529/20000000000000000000000000000 : ℝ)*base67 + (16833297960471/20000000000000000000000000000 : ℝ)*base70 + (23786563199529/20000000000000000000000000000 : ℝ)*base71 + (5074897859529/10000000000000000000000000000 : ℝ)*base73 + (129249803999529/20000000000000000000000000000 : ℝ)*base75 + (61887371220471/20000000000000000000000000000 : ℝ)*base78 + (6792949679529/20000000000000000000000000000 : ℝ)*base79 + (3014093659529/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4656043/5000000000000000000000 : ℝ)*base90 + (4656043/5000000000000000000000 : ℝ)*base92 + (4656043/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128857075690173132133983/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1088723909/100000000000000 : ℝ)*(base19) + (73150699/6250000000000 : ℝ)*(base23) + (3096471/4000000000000 : ℝ)*(base39) + (156623149/100000000000000 : ℝ)*(upper3) + (23443237/12500000000000 : ℝ)*(upper5) + (366241159340051/50000000000000 : ℝ)*(major0) + (366241159340051/50000000000000 : ℝ)*(major1) + (366241120634163/50000000000000 : ℝ)*(major2) + (597746577/20000000000000 : ℝ)*(sp1) + (3234332563/100000000000000 : ℝ)*(sp2) + (1021194448003391/100000000000000 : ℝ)*(sp4) + (1021190370546597/100000000000000 : ℝ)*(sp5) + (1021190120671419/100000000000000 : ℝ)*(sp6) + (110942485033899/25000000000000 : ℝ)*(sp7) + (110942485033899/25000000000000 : ℝ)*(f.failure) + (510597262707583/50000000000000 : ℝ)*(f.sum) + (66230691030339/50000000000000000000000000000 : ℝ)*base65 + (283049184048451/100000000000000000000000000000 : ℝ)*base67 + (119409420687773/100000000000000000000000000000 : ℝ)*base70 + (505669993248451/100000000000000000000000000000 : ℝ)*base71 + (100466252319661/50000000000000000000000000000 : ℝ)*base74 + (21482928887773/100000000000000000000000000000 : ℝ)*base76 + (629914011112227/100000000000000000000000000000 : ℝ)*base77 + (753172143412227/100000000000000000000000000000 : ℝ)*base79 + (125460027862227/50000000000000000000000000000 : ℝ)*base81 + (29247121/2500000000000000000000 : ℝ)*base90 + (29247121/2500000000000000000000 : ℝ)*base92 + (4247121/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1533_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1547/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5043/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1533_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1533_s1_0 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-362385069/2000000000 : ℝ)*x 0 + (1111387389/2000000000 : ℝ)*x 1 + (1277199607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (362385069/2000000000 : ℝ)^4563 ≤ (2210625697597/20000000000000 : ℝ)^3539 := by
    have hnat : (362385069 : ℕ)^4563*20000000000000^3539 ≤ 2210625697597^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362385069 2000000000 2210625697597 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111387389/2000000000 : ℝ)^4563 ≤ (23440901603121/50000000000000 : ℝ)^3539 := by
    have hnat : (1111387389 : ℕ)^4563*50000000000000^3539 ≤ 23440901603121^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111387389 2000000000 23440901603121 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277199607/2500000000 : ℝ)^4563 ≤ (42065068289729/100000000000000 : ℝ)^3539 := by
    have hnat : (1277199607 : ℕ)^4563*100000000000000^3539 ≤ 42065068289729^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277199607 2500000000 42065068289729 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-362385069/2000000000 : ℝ), (1111387389/2000000000 : ℝ), (1277199607/2500000000 : ℝ)] ![(2210625697597/20000000000000 : ℝ), (23440901603121/50000000000000 : ℝ), (42065068289729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-362385069/2000000000 : ℝ)|^4563 ≤ (2210625697597/20000000000000 : ℝ)^3539
        have hw : |(-362385069/2000000000 : ℝ)|=(362385069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1111387389/2000000000 : ℝ)|^4563 ≤ (23440901603121/50000000000000 : ℝ)^3539
        have hw : |(1111387389/2000000000 : ℝ)|=(1111387389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1277199607/2500000000 : ℝ)|^4563 ≤ (42065068289729/100000000000000 : ℝ)^3539
        have hw : |(1277199607/2500000000 : ℝ)|=(1277199607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s1_1 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382845051/10000000000 : ℝ)*x 0 + (-2047299419/10000000000 : ℝ)*x 1 + (5108799941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382845051/10000000000 : ℝ)^4563 ≤ (44996724316203/100000000000000 : ℝ)^3539 := by
    have hnat : (5382845051 : ℕ)^4563*100000000000000^3539 ≤ 44996724316203^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382845051 10000000000 44996724316203 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047299419/10000000000 : ℝ)^4563 ≤ (323454783001/2500000000000 : ℝ)^3539 := by
    have hnat : (2047299419 : ℕ)^4563*2500000000000^3539 ≤ 323454783001^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047299419 10000000000 323454783001 2500000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5108799941/10000000000 : ℝ)^4563 ≤ (1682603374087/4000000000000 : ℝ)^3539 := by
    have hnat : (5108799941 : ℕ)^4563*4000000000000^3539 ≤ 1682603374087^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5108799941 10000000000 1682603374087 4000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382845051/10000000000 : ℝ), (-2047299419/10000000000 : ℝ), (5108799941/10000000000 : ℝ)] ![(44996724316203/100000000000000 : ℝ), (323454783001/2500000000000 : ℝ), (1682603374087/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382845051/10000000000 : ℝ)|^4563 ≤ (44996724316203/100000000000000 : ℝ)^3539
        have hw : |(5382845051/10000000000 : ℝ)|=(5382845051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047299419/10000000000 : ℝ)|^4563 ≤ (323454783001/2500000000000 : ℝ)^3539
        have hw : |(-2047299419/10000000000 : ℝ)|=(2047299419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5108799941/10000000000 : ℝ)|^4563 ≤ (1682603374087/4000000000000 : ℝ)^3539
        have hw : |(5108799941/10000000000 : ℝ)|=(5108799941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s1_2 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345711621/2500000000 : ℝ)*x 0 + (638599759/1250000000 : ℝ)*x 1 + (-1023649979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345711621/2500000000 : ℝ)^4563 ≤ (2812296235069/6250000000000 : ℝ)^3539 := by
    have hnat : (1345711621 : ℕ)^4563*6250000000000^3539 ≤ 2812296235069^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345711621 2500000000 2812296235069 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (638599759/1250000000 : ℝ)^4563 ≤ (4206506451033/10000000000000 : ℝ)^3539 := by
    have hnat : (638599759 : ℕ)^4563*10000000000000^3539 ≤ 4206506451033^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638599759 1250000000 4206506451033 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023649979/5000000000 : ℝ)^4563 ≤ (517527828477/4000000000000 : ℝ)^3539 := by
    have hnat : (1023649979 : ℕ)^4563*4000000000000^3539 ≤ 517527828477^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023649979 5000000000 517527828477 4000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345711621/2500000000 : ℝ), (638599759/1250000000 : ℝ), (-1023649979/5000000000 : ℝ)] ![(2812296235069/6250000000000 : ℝ), (4206506451033/10000000000000 : ℝ), (517527828477/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345711621/2500000000 : ℝ)|^4563 ≤ (2812296235069/6250000000000 : ℝ)^3539
        have hw : |(1345711621/2500000000 : ℝ)|=(1345711621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(638599759/1250000000 : ℝ)|^4563 ≤ (4206506451033/10000000000000 : ℝ)^3539
        have hw : |(638599759/1250000000 : ℝ)|=(638599759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023649979/5000000000 : ℝ)|^4563 ≤ (517527828477/4000000000000 : ℝ)^3539
        have hw : |(-1023649979/5000000000 : ℝ)|=(1023649979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s1_3 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4241947459/10000000000 : ℝ)*x 0 + (3752342527/10000000000 : ℝ)*x 1 + (2391793863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241947459/10000000000 : ℝ)^4563 ≤ (33098042994681/100000000000000 : ℝ)^3539 := by
    have hnat : (4241947459 : ℕ)^4563*100000000000000^3539 ≤ 33098042994681^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241947459 10000000000 33098042994681 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3752342527/10000000000 : ℝ)^4563 ≤ (28257130510401/100000000000000 : ℝ)^3539 := by
    have hnat : (3752342527 : ℕ)^4563*100000000000000^3539 ≤ 28257130510401^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752342527 10000000000 28257130510401 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2391793863/5000000000 : ℝ)^4563 ≤ (19322413240533/50000000000000 : ℝ)^3539 := by
    have hnat : (2391793863 : ℕ)^4563*50000000000000^3539 ≤ 19322413240533^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391793863 5000000000 19322413240533 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241947459/10000000000 : ℝ), (3752342527/10000000000 : ℝ), (2391793863/5000000000 : ℝ)] ![(33098042994681/100000000000000 : ℝ), (28257130510401/100000000000000 : ℝ), (19322413240533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241947459/10000000000 : ℝ)|^4563 ≤ (33098042994681/100000000000000 : ℝ)^3539
        have hw : |(4241947459/10000000000 : ℝ)|=(4241947459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3752342527/10000000000 : ℝ)|^4563 ≤ (28257130510401/100000000000000 : ℝ)^3539
        have hw : |(3752342527/10000000000 : ℝ)|=(3752342527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2391793863/5000000000 : ℝ)|^4563 ≤ (19322413240533/50000000000000 : ℝ)^3539
        have hw : |(2391793863/5000000000 : ℝ)|=(2391793863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s1_4 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1812190111/10000000000 : ℝ)*x 0 + (5113664891/10000000000 : ℝ)*x 1 + (2775997357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1812190111/10000000000 : ℝ)^4563 ≤ (2211042198757/20000000000000 : ℝ)^3539 := by
    have hnat : (1812190111 : ℕ)^4563*20000000000000^3539 ≤ 2211042198757^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812190111 10000000000 2211042198757 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5113664891/10000000000 : ℝ)^4563 ≤ (42116739186097/100000000000000 : ℝ)^3539 := by
    have hnat : (5113664891 : ℕ)^4563*100000000000000^3539 ≤ 42116739186097^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113664891 10000000000 42116739186097 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2775997357/5000000000 : ℝ)^4563 ≤ (46828049812441/100000000000000 : ℝ)^3539 := by
    have hnat : (2775997357 : ℕ)^4563*100000000000000^3539 ≤ 46828049812441^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775997357 5000000000 46828049812441 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1812190111/10000000000 : ℝ), (5113664891/10000000000 : ℝ), (2775997357/5000000000 : ℝ)] ![(2211042198757/20000000000000 : ℝ), (42116739186097/100000000000000 : ℝ), (46828049812441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1812190111/10000000000 : ℝ)|^4563 ≤ (2211042198757/20000000000000 : ℝ)^3539
        have hw : |(-1812190111/10000000000 : ℝ)|=(1812190111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5113664891/10000000000 : ℝ)|^4563 ≤ (42116739186097/100000000000000 : ℝ)^3539
        have hw : |(5113664891/10000000000 : ℝ)|=(5113664891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2775997357/5000000000 : ℝ)|^4563 ≤ (46828049812441/100000000000000 : ℝ)^3539
        have hw : |(2775997357/5000000000 : ℝ)|=(2775997357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s1_5 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658065113/1250000000 : ℝ)*x 0 + (-200512931/1250000000 : ℝ)*x 1 + (5551994803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658065113/1250000000 : ℝ)^4563 ≤ (43725501460067/100000000000000 : ℝ)^3539 := by
    have hnat : (658065113 : ℕ)^4563*100000000000000^3539 ≤ 43725501460067^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658065113 1250000000 43725501460067 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200512931/1250000000 : ℝ)^4563 ≤ (9446447742447/100000000000000 : ℝ)^3539 := by
    have hnat : (200512931 : ℕ)^4563*100000000000000^3539 ≤ 9446447742447^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200512931 1250000000 9446447742447 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5551994803/10000000000 : ℝ)^4563 ≤ (4682805078031/10000000000000 : ℝ)^3539 := by
    have hnat : (5551994803 : ℕ)^4563*10000000000000^3539 ≤ 4682805078031^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5551994803 10000000000 4682805078031 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658065113/1250000000 : ℝ), (-200512931/1250000000 : ℝ), (5551994803/10000000000 : ℝ)] ![(43725501460067/100000000000000 : ℝ), (9446447742447/100000000000000 : ℝ), (4682805078031/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658065113/1250000000 : ℝ)|^4563 ≤ (43725501460067/100000000000000 : ℝ)^3539
        have hw : |(658065113/1250000000 : ℝ)|=(658065113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200512931/1250000000 : ℝ)|^4563 ≤ (9446447742447/100000000000000 : ℝ)^3539
        have hw : |(-200512931/1250000000 : ℝ)|=(200512931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5551994803/10000000000 : ℝ)|^4563 ≤ (4682805078031/10000000000000 : ℝ)^3539
        have hw : |(5551994803/10000000000 : ℝ)|=(5551994803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s1_6 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526452091/1000000000 : ℝ)*x 0 + (346999679/625000000 : ℝ)*x 1 + (-1604103353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526452091/1000000000 : ℝ)^4563 ≤ (273284384527/625000000000 : ℝ)^3539 := by
    have hnat : (526452091 : ℕ)^4563*625000000000^3539 ≤ 273284384527^3539*1000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526452091 1000000000 273284384527 625000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346999679/625000000 : ℝ)^4563 ≤ (23414025721841/50000000000000 : ℝ)^3539 := by
    have hnat : (346999679 : ℕ)^4563*50000000000000^3539 ≤ 23414025721841^3539*625000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346999679 625000000 23414025721841 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1604103353/10000000000 : ℝ)^4563 ≤ (2361611755281/25000000000000 : ℝ)^3539 := by
    have hnat : (1604103353 : ℕ)^4563*25000000000000^3539 ≤ 2361611755281^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604103353 10000000000 2361611755281 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526452091/1000000000 : ℝ), (346999679/625000000 : ℝ), (-1604103353/10000000000 : ℝ)] ![(273284384527/625000000000 : ℝ), (23414025721841/50000000000000 : ℝ), (2361611755281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526452091/1000000000 : ℝ)|^4563 ≤ (273284384527/625000000000 : ℝ)^3539
        have hw : |(526452091/1000000000 : ℝ)|=(526452091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346999679/625000000 : ℝ)|^4563 ≤ (23414025721841/50000000000000 : ℝ)^3539
        have hw : |(346999679/625000000 : ℝ)|=(346999679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1604103353/10000000000 : ℝ)|^4563 ≤ (2361611755281/25000000000000 : ℝ)^3539
        have hw : |(-1604103353/10000000000 : ℝ)|=(1604103353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s1_7 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121279261/5000000000 : ℝ)*x 0 + (2386194893/5000000000 : ℝ)*x 1 + (3763713289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121279261/5000000000 : ℝ)^4563 ≤ (6620838108669/20000000000000 : ℝ)^3539 := by
    have hnat : (2121279261 : ℕ)^4563*20000000000000^3539 ≤ 6620838108669^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121279261 5000000000 6620838108669 20000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2386194893/5000000000 : ℝ)^4563 ≤ (38528226501871/100000000000000 : ℝ)^3539 := by
    have hnat : (2386194893 : ℕ)^4563*100000000000000^3539 ≤ 38528226501871^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386194893 5000000000 38528226501871 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3763713289/10000000000 : ℝ)^4563 ≤ (28367582940863/100000000000000 : ℝ)^3539 := by
    have hnat : (3763713289 : ℕ)^4563*100000000000000^3539 ≤ 28367582940863^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3763713289 10000000000 28367582940863 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121279261/5000000000 : ℝ), (2386194893/5000000000 : ℝ), (3763713289/10000000000 : ℝ)] ![(6620838108669/20000000000000 : ℝ), (38528226501871/100000000000000 : ℝ), (28367582940863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121279261/5000000000 : ℝ)|^4563 ≤ (6620838108669/20000000000000 : ℝ)^3539
        have hw : |(2121279261/5000000000 : ℝ)|=(2121279261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2386194893/5000000000 : ℝ)|^4563 ≤ (38528226501871/100000000000000 : ℝ)^3539
        have hw : |(2386194893/5000000000 : ℝ)|=(2386194893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3763713289/10000000000 : ℝ)|^4563 ≤ (28367582940863/100000000000000 : ℝ)^3539
        have hw : |(3763713289/10000000000 : ℝ)|=(3763713289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1533_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5043/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8629/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (566/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5043/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1547/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5043/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1547/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5043/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1547/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5043/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1547/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5043/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1547/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5043/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1547/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1547/50000 : ℝ) ^ (4561/1024 : ℝ) ≤ (3781413297099/20000000000000000000 : ℝ) := by
    have hpowers : (1547/50000 : ℝ)^4561 ≤ (3781413297099/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1547 : ℕ)^4561*20000000000000000000^1024 ≤ 3781413297099^1024*50000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1547 50000 3781413297099 20000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1547/50000 : ℝ)) (X := (3781413297099/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5043/20000 : ℝ) ^ (4561/1024 : ℝ) ≤ (54059036773876059/25000000000000000000 : ℝ) := by
    have hpowers : (5043/20000 : ℝ)^4561 ≤ (54059036773876059/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5043 : ℕ)^4561*25000000000000000000^1024 ≤ 54059036773876059^1024*20000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5043 20000 54059036773876059 25000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5043/20000 : ℝ)) (X := (54059036773876059/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000003781413297099/10000000000000000000 : ℝ) ≤ (400000033958927/400000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (10000003781413297099/10000000000000000000 : ℝ)^1024 ≤ (400000033958927/400000000000000 : ℝ)^4561 := by
      have hnat : (10000003781413297099 : ℕ)^1024*400000000000000^4561 ≤ 400000033958927^4561*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000003781413297099 10000000000000000000 400000033958927 400000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000033958927/400000000000000 : ℝ)) (X := (10000003781413297099/10000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100216255054161989731/100000000000000000000 : ℝ) ≤ (250121278079081/250000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (100216255054161989731/100000000000000000000 : ℝ)^1024 ≤ (250121278079081/250000000000000 : ℝ)^4561 := by
      have hnat : (100216255054161989731 : ℕ)^1024*250000000000000^4561 ≤ 250121278079081^4561*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100216255054161989731 100000000000000000000 250121278079081 250000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250121278079081/250000000000000 : ℝ)) (X := (100216255054161989731/100000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12554059036773876059/12500000000000000000 : ℝ) ≤ (2001940279470661/2000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (12554059036773876059/12500000000000000000 : ℝ)^1024 ≤ (2001940279470661/2000000000000000 : ℝ)^4561 := by
      have hnat : (12554059036773876059 : ℕ)^1024*2000000000000000^4561 ≤ 2001940279470661^4561*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12554059036773876059 12500000000000000000 2001940279470661 2000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001940279470661/2000000000000000 : ℝ)) (X := (12554059036773876059/12500000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3781413297099/20000000000000000000 : ℝ) ≤ ((44236001056689496391/44242000000000000000 : ℝ)+2*(970054838013/442420000000000 : ℝ)*(1547/50000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (44236001056689496391/44242000000000000000 : ℝ)+2*(970054838013/442420000000000 : ℝ)*(1547/50000 : ℝ)=(400000033958927/400000000000000 : ℝ) by norm_num, show 1+2*(3781413297099/20000000000000000000 : ℝ)=(10000003781413297099/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54059036773876059/25000000000000000000 : ℝ)+(3781413297099/20000000000000000000 : ℝ) ≤ ((44236001056689496391/44242000000000000000 : ℝ)+(970054838013/442420000000000 : ℝ)*((5043/20000 : ℝ)+(1547/50000 : ℝ)))^(4561/1024 : ℝ) := by
    rw [show (44236001056689496391/44242000000000000000 : ℝ)+(970054838013/442420000000000 : ℝ)*((5043/20000 : ℝ)+(1547/50000 : ℝ))=(250121278079081/250000000000000 : ℝ) by norm_num, show 1+(54059036773876059/25000000000000000000 : ℝ)+(3781413297099/20000000000000000000 : ℝ)=(100216255054161989731/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54059036773876059/25000000000000000000 : ℝ) ≤ ((44236001056689496391/44242000000000000000 : ℝ)+2*(970054838013/442420000000000 : ℝ)*(5043/20000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (44236001056689496391/44242000000000000000 : ℝ)+2*(970054838013/442420000000000 : ℝ)*(5043/20000 : ℝ)=(2001940279470661/2000000000000000 : ℝ) by norm_num, show 1+2*(54059036773876059/25000000000000000000 : ℝ)=(12554059036773876059/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44236001056689496391/44242000000000000000 : ℝ)*(X 1 0+X 2 0)+(970054838013/442420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (1547/50000 : ℝ)) (hi := (5043/20000 : ℝ)) (c := (44236001056689496391/44242000000000000000 : ℝ)) (alpha := (970054838013/442420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44236001056689496391/44242000000000000000 : ℝ)*(X 0 1+X 2 1)+(970054838013/442420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (1547/50000 : ℝ)) (hi := (5043/20000 : ℝ)) (c := (44236001056689496391/44242000000000000000 : ℝ)) (alpha := (970054838013/442420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44236001056689496391/44242000000000000000 : ℝ)*(X 0 2+X 1 2)+(970054838013/442420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (1547/50000 : ℝ)) (hi := (5043/20000 : ℝ)) (c := (44236001056689496391/44242000000000000000 : ℝ)) (alpha := (970054838013/442420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-362385069/2000000000 : ℝ)*X 0 0+(1111387389/2000000000 : ℝ)*X 0 1+(1277199607/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5382845051/10000000000 : ℝ)*X 1 0+(-2047299419/10000000000 : ℝ)*X 1 1+(5108799941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1345711621/2500000000 : ℝ)*X 2 0+(638599759/1250000000 : ℝ)*X 2 1+(-1023649979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4241947459/10000000000 : ℝ)*X 0 0+(3752342527/10000000000 : ℝ)*X 0 1+(2391793863/5000000000 : ℝ)*X 0 2+(4241947459/10000000000 : ℝ)*X 1 0+(3752342527/10000000000 : ℝ)*X 1 1+(2391793863/5000000000 : ℝ)*X 1 2+(4241947459/10000000000 : ℝ)*X 2 0+(3752342527/10000000000 : ℝ)*X 2 1+(2391793863/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1812190111/10000000000 : ℝ)*X 0 0+(5113664891/10000000000 : ℝ)*X 0 1+(2775997357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((658065113/1250000000 : ℝ)*X 1 0+(-200512931/1250000000 : ℝ)*X 1 1+(5551994803/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526452091/1000000000 : ℝ)*X 2 0+(346999679/625000000 : ℝ)*X 2 1+(-1604103353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121279261/5000000000 : ℝ)*X 0 0+(2386194893/5000000000 : ℝ)*X 0 1+(3763713289/10000000000 : ℝ)*X 0 2+(2121279261/5000000000 : ℝ)*X 1 0+(2386194893/5000000000 : ℝ)*X 1 1+(3763713289/10000000000 : ℝ)*X 1 2+(2121279261/5000000000 : ℝ)*X 2 0+(2386194893/5000000000 : ℝ)*X 2 1+(3763713289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (890793646217106792261543909/100550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (682557571/100000000000000 : ℝ)*(base19) + (1167556087/100000000000000 : ℝ)*(base23) + (13237233/50000000000000 : ℝ)*(upper2) + (31092531/12500000000000 : ℝ)*(upper3) + (85177239/100000000000000 : ℝ)*(upper4) + (1600590927821237/100000000000000 : ℝ)*(major0) + (1600590927821237/100000000000000 : ℝ)*(major1) + (1600590927821237/100000000000000 : ℝ)*(major2) + (2231463781833921/100000000000000 : ℝ)*(sp0) + (557868159395863/25000000000000 : ℝ)*(sp1) + (278934019073117/12500000000000 : ℝ)*(sp2) + (969703708301149/100000000000000 : ℝ)*(sp3) + (4769153551/50000000000000 : ℝ)*(sp4) + (453189327/10000000000000 : ℝ)*(sp7) + (969708240194419/100000000000000 : ℝ)*(f.failure) + (2231473320141023/100000000000000 : ℝ)*(f.sum) + (3541955223533/2011000000000000000000000000 : ℝ)*base66 + (1846122523558068697/402200000000000000000000000000000 : ℝ)*base67 + (1827811865808068697/402200000000000000000000000000000 : ℝ)*base69 + (900670013049468697/402200000000000000000000000000000 : ℝ)*base71 + (1458680252733/1005500000000000000000000000 : ℝ)*base73 + (787866928512868697/402200000000000000000000000000000 : ℝ)*base75 + (330572367488931303/402200000000000000000000000000000 : ℝ)*base78 + (2521586789995068697/402200000000000000000000000000000 : ℝ)*base79 + (1480241288339/402200000000000000000000000 : ℝ)*base81 + (50196201/10000000000000000000000 : ℝ)*base90 + (50196201/10000000000000000000000 : ℝ)*base92 + (50196201/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4091297981281693826296562829/553025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154487209/12500000000000 : ℝ)*(base19) + (275743717/20000000000000 : ℝ)*(base23) + (192127627/100000000000000 : ℝ)*(upper3) + (53138473/100000000000000 : ℝ)*(lower4) + (145947847/100000000000000 : ℝ)*(upper5) + (409098069230509/25000000000000 : ℝ)*(major0) + (409098069230509/25000000000000 : ℝ)*(major1) + (409098069230509/25000000000000 : ℝ)*(major2) + (8526827981/100000000000000 : ℝ)*(sp1) + (2054907069/20000000000000 : ℝ)*(sp2) + (2281386038303687/100000000000000 : ℝ)*(sp4) + (1140688137789017/50000000000000 : ℝ)*(sp5) + (570343596262439/25000000000000 : ℝ)*(sp6) + (991398268939227/100000000000000 : ℝ)*(sp7) + (991398268939227/100000000000000 : ℝ)*(f.failure) + (2281386038303687/100000000000000 : ℝ)*(f.sum) + (89170601848791/22121000000000000000000000000 : ℝ)*base65 + (11127908298403343019/1106050000000000000000000000000000 : ℝ)*base67 + (9178042155232243019/1106050000000000000000000000000000 : ℝ)*base69 + (4024248284435243019/1106050000000000000000000000000000 : ℝ)*base71 + (146018742263197/22121000000000000000000000000 : ℝ)*base73 + (3550243074506993019/1106050000000000000000000000000000 : ℝ)*base75 + (9013661764088593019/1106050000000000000000000000000000 : ℝ)*base77 + (11658198543515993019/1106050000000000000000000000000000 : ℝ)*base79 + (66582030537243/22121000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (82883233/10000000000000000000000 : ℝ)*base90 + (82883233/10000000000000000000000 : ℝ)*base92 + (82883233/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1533_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5043/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8629/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (566/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1533_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1533_s2_0 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1834130921/10000000000 : ℝ)*x 0 + (1090298717/2000000000 : ℝ)*x 1 + (5199826459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1834130921/10000000000 : ℝ)^4563 ≤ (701755661543/6250000000000 : ℝ)^3539 := by
    have hnat : (1834130921 : ℕ)^4563*6250000000000^3539 ≤ 701755661543^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834130921 10000000000 701755661543 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090298717/2000000000 : ℝ)^4563 ≤ (22868990266387/50000000000000 : ℝ)^3539 := by
    have hnat : (1090298717 : ℕ)^4563*50000000000000^3539 ≤ 22868990266387^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090298717 2000000000 22868990266387 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5199826459/10000000000 : ℝ)^4563 ≤ (21516964431443/50000000000000 : ℝ)^3539 := by
    have hnat : (5199826459 : ℕ)^4563*50000000000000^3539 ≤ 21516964431443^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199826459 10000000000 21516964431443 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1834130921/10000000000 : ℝ), (1090298717/2000000000 : ℝ), (5199826459/10000000000 : ℝ)] ![(701755661543/6250000000000 : ℝ), (22868990266387/50000000000000 : ℝ), (21516964431443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1834130921/10000000000 : ℝ)|^4563 ≤ (701755661543/6250000000000 : ℝ)^3539
        have hw : |(-1834130921/10000000000 : ℝ)|=(1834130921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090298717/2000000000 : ℝ)|^4563 ≤ (22868990266387/50000000000000 : ℝ)^3539
        have hw : |(1090298717/2000000000 : ℝ)|=(1090298717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5199826459/10000000000 : ℝ)|^4563 ≤ (21516964431443/50000000000000 : ℝ)^3539
        have hw : |(5199826459/10000000000 : ℝ)|=(5199826459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s2_1 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338971131/2500000000 : ℝ)*x 0 + (-1963531527/10000000000 : ℝ)*x 1 + (1299956701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338971131/2500000000 : ℝ)^4563 ≤ (11176588516297/25000000000000 : ℝ)^3539 := by
    have hnat : (1338971131 : ℕ)^4563*25000000000000^3539 ≤ 11176588516297^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338971131 2500000000 11176588516297 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1963531527/10000000000 : ℝ)^4563 ≤ (12259713375453/100000000000000 : ℝ)^3539 := by
    have hnat : (1963531527 : ℕ)^4563*100000000000000^3539 ≤ 12259713375453^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963531527 10000000000 12259713375453 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299956701/2500000000 : ℝ)^4563 ≤ (4303393254427/10000000000000 : ℝ)^3539 := by
    have hnat : (1299956701 : ℕ)^4563*10000000000000^3539 ≤ 4303393254427^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299956701 2500000000 4303393254427 10000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338971131/2500000000 : ℝ), (-1963531527/10000000000 : ℝ), (1299956701/2500000000 : ℝ)] ![(11176588516297/25000000000000 : ℝ), (12259713375453/100000000000000 : ℝ), (4303393254427/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338971131/2500000000 : ℝ)|^4563 ≤ (11176588516297/25000000000000 : ℝ)^3539
        have hw : |(1338971131/2500000000 : ℝ)|=(1338971131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1963531527/10000000000 : ℝ)|^4563 ≤ (12259713375453/100000000000000 : ℝ)^3539
        have hw : |(-1963531527/10000000000 : ℝ)|=(1963531527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299956701/2500000000 : ℝ)|^4563 ≤ (4303393254427/10000000000000 : ℝ)^3539
        have hw : |(1299956701/2500000000 : ℝ)|=(1299956701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s2_2 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071177041/2000000000 : ℝ)*x 0 + (5199826411/10000000000 : ℝ)*x 1 + (-981765569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071177041/2000000000 : ℝ)^4563 ≤ (22353180697181/50000000000000 : ℝ)^3539 := by
    have hnat : (1071177041 : ℕ)^4563*50000000000000^3539 ≤ 22353180697181^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071177041 2000000000 22353180697181 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5199826411/10000000000 : ℝ)^4563 ≤ (43033928350693/100000000000000 : ℝ)^3539 := by
    have hnat : (5199826411 : ℕ)^4563*100000000000000^3539 ≤ 43033928350693^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199826411 10000000000 43033928350693 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (981765569/5000000000 : ℝ)^4563 ≤ (3064927560971/25000000000000 : ℝ)^3539 := by
    have hnat : (981765569 : ℕ)^4563*25000000000000^3539 ≤ 3064927560971^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981765569 5000000000 3064927560971 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071177041/2000000000 : ℝ), (5199826411/10000000000 : ℝ), (-981765569/5000000000 : ℝ)] ![(22353180697181/50000000000000 : ℝ), (43033928350693/100000000000000 : ℝ), (3064927560971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071177041/2000000000 : ℝ)|^4563 ≤ (22353180697181/50000000000000 : ℝ)^3539
        have hw : |(1071177041/2000000000 : ℝ)|=(1071177041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5199826411/10000000000 : ℝ)|^4563 ≤ (43033928350693/100000000000000 : ℝ)^3539
        have hw : |(5199826411/10000000000 : ℝ)|=(5199826411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-981765569/5000000000 : ℝ)|^4563 ≤ (3064927560971/25000000000000 : ℝ)^3539
        have hw : |(-981765569/5000000000 : ℝ)|=(981765569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s2_3 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85158937/200000000 : ℝ)*x 0 + (994147461/2500000000 : ℝ)*x 1 + (2277861357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85158937/200000000 : ℝ)^4563 ≤ (33259087938081/100000000000000 : ℝ)^3539 := by
    have hnat : (85158937 : ℕ)^4563*100000000000000^3539 ≤ 33259087938081^3539*200000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85158937 200000000 33259087938081 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994147461/2500000000 : ℝ)^4563 ≤ (7613254527181/25000000000000 : ℝ)^3539 := by
    have hnat : (994147461 : ℕ)^4563*25000000000000^3539 ≤ 7613254527181^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994147461 2500000000 7613254527181 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277861357/5000000000 : ℝ)^4563 ≤ (18143946966771/50000000000000 : ℝ)^3539 := by
    have hnat : (2277861357 : ℕ)^4563*50000000000000^3539 ≤ 18143946966771^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277861357 5000000000 18143946966771 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85158937/200000000 : ℝ), (994147461/2500000000 : ℝ), (2277861357/5000000000 : ℝ)] ![(33259087938081/100000000000000 : ℝ), (7613254527181/25000000000000 : ℝ), (18143946966771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85158937/200000000 : ℝ)|^4563 ≤ (33259087938081/100000000000000 : ℝ)^3539
        have hw : |(85158937/200000000 : ℝ)|=(85158937/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994147461/2500000000 : ℝ)|^4563 ≤ (7613254527181/25000000000000 : ℝ)^3539
        have hw : |(994147461/2500000000 : ℝ)|=(994147461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2277861357/5000000000 : ℝ)|^4563 ≤ (18143946966771/50000000000000 : ℝ)^3539
        have hw : |(2277861357/5000000000 : ℝ)|=(2277861357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s2_4 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-458544419/2500000000 : ℝ)*x 0 + (650171161/1250000000 : ℝ)*x 1 + (5449937467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458544419/2500000000 : ℝ)^4563 ≤ (5614229813067/50000000000000 : ℝ)^3539 := by
    have hnat : (458544419 : ℕ)^4563*50000000000000^3539 ≤ 5614229813067^3539*2500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458544419 2500000000 5614229813067 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650171161/1250000000 : ℝ)^4563 ≤ (43050392602487/100000000000000 : ℝ)^3539 := by
    have hnat : (650171161 : ℕ)^4563*100000000000000^3539 ≤ 43050392602487^3539*1250000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650171161 1250000000 43050392602487 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449937467/10000000000 : ℝ)^4563 ≤ (45721147747793/100000000000000 : ℝ)^3539 := by
    have hnat : (5449937467 : ℕ)^4563*100000000000000^3539 ≤ 45721147747793^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449937467 10000000000 45721147747793 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458544419/2500000000 : ℝ), (650171161/1250000000 : ℝ), (5449937467/10000000000 : ℝ)] ![(5614229813067/50000000000000 : ℝ), (43050392602487/100000000000000 : ℝ), (45721147747793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458544419/2500000000 : ℝ)|^4563 ≤ (5614229813067/50000000000000 : ℝ)^3539
        have hw : |(-458544419/2500000000 : ℝ)|=(458544419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650171161/1250000000 : ℝ)|^4563 ≤ (43050392602487/100000000000000 : ℝ)^3539
        have hw : |(650171161/1250000000 : ℝ)|=(650171161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449937467/10000000000 : ℝ)|^4563 ≤ (45721147747793/100000000000000 : ℝ)^3539
        have hw : |(5449937467/10000000000 : ℝ)|=(5449937467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s2_5 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057921217/2000000000 : ℝ)*x 0 + (-1713420363/10000000000 : ℝ)*x 1 + (1089987463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057921217/2000000000 : ℝ)^4563 ≤ (43994321744157/100000000000000 : ℝ)^3539 := by
    have hnat : (1057921217 : ℕ)^4563*100000000000000^3539 ≤ 43994321744157^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057921217 2000000000 43994321744157 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1713420363/10000000000 : ℝ)^4563 ≤ (5142266066069/50000000000000 : ℝ)^3539 := by
    have hnat : (1713420363 : ℕ)^4563*50000000000000^3539 ≤ 5142266066069^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713420363 10000000000 5142266066069 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089987463/2000000000 : ℝ)^4563 ≤ (11430286525913/25000000000000 : ℝ)^3539 := by
    have hnat : (1089987463 : ℕ)^4563*25000000000000^3539 ≤ 11430286525913^3539*2000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089987463 2000000000 11430286525913 25000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057921217/2000000000 : ℝ), (-1713420363/10000000000 : ℝ), (1089987463/2000000000 : ℝ)] ![(43994321744157/100000000000000 : ℝ), (5142266066069/50000000000000 : ℝ), (11430286525913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057921217/2000000000 : ℝ)|^4563 ≤ (43994321744157/100000000000000 : ℝ)^3539
        have hw : |(1057921217/2000000000 : ℝ)|=(1057921217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1713420363/10000000000 : ℝ)|^4563 ≤ (5142266066069/50000000000000 : ℝ)^3539
        have hw : |(-1713420363/10000000000 : ℝ)|=(1713420363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089987463/2000000000 : ℝ)|^4563 ≤ (11430286525913/25000000000000 : ℝ)^3539
        have hw : |(1089987463/2000000000 : ℝ)|=(1089987463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s2_6 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264480287/500000000 : ℝ)*x 0 + (2724968749/5000000000 : ℝ)*x 1 + (-1713420587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264480287/500000000 : ℝ)^4563 ≤ (43994318044493/100000000000000 : ℝ)^3539 := by
    have hnat : (264480287 : ℕ)^4563*100000000000000^3539 ≤ 43994318044493^3539*500000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264480287 500000000 43994318044493 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724968749/5000000000 : ℝ)^4563 ≤ (5715143510389/12500000000000 : ℝ)^3539 := by
    have hnat : (2724968749 : ℕ)^4563*12500000000000^3539 ≤ 5715143510389^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724968749 5000000000 5715143510389 12500000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1713420587/10000000000 : ℝ)^4563 ≤ (10284533865697/100000000000000 : ℝ)^3539 := by
    have hnat : (1713420587 : ℕ)^4563*100000000000000^3539 ≤ 10284533865697^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713420587 10000000000 10284533865697 100000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264480287/500000000 : ℝ), (2724968749/5000000000 : ℝ), (-1713420587/10000000000 : ℝ)] ![(43994318044493/100000000000000 : ℝ), (5715143510389/12500000000000 : ℝ), (10284533865697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264480287/500000000 : ℝ)|^4563 ≤ (43994318044493/100000000000000 : ℝ)^3539
        have hw : |(264480287/500000000 : ℝ)|=(264480287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724968749/5000000000 : ℝ)|^4563 ≤ (5715143510389/12500000000000 : ℝ)^3539
        have hw : |(2724968749/5000000000 : ℝ)|=(2724968749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1713420587/10000000000 : ℝ)|^4563 ≤ (10284533865697/100000000000000 : ℝ)^3539
        have hw : |(-1713420587/10000000000 : ℝ)|=(1713420587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1533_s2_7 (p : ℝ) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4258055271/10000000000 : ℝ)*x 0 + (4552171483/10000000000 : ℝ)*x 1 + (1990086047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258055271/10000000000 : ℝ)^4563 ≤ (2078761241789/6250000000000 : ℝ)^3539 := by
    have hnat : (4258055271 : ℕ)^4563*6250000000000^3539 ≤ 2078761241789^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258055271 10000000000 2078761241789 6250000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4552171483/10000000000 : ℝ)^4563 ≤ (4531428321729/12500000000000 : ℝ)^3539 := by
    have hnat : (4552171483 : ℕ)^4563*12500000000000^3539 ≤ 4531428321729^3539*10000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4552171483 10000000000 4531428321729 12500000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1990086047/5000000000 : ℝ)^4563 ≤ (15244196777353/50000000000000 : ℝ)^3539 := by
    have hnat : (1990086047 : ℕ)^4563*50000000000000^3539 ≤ 15244196777353^3539*5000000000^4563 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990086047 5000000000 15244196777353 50000000000000 4563 3539 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4563/1024 : ℝ)) 4563 3539 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258055271/10000000000 : ℝ), (4552171483/10000000000 : ℝ), (1990086047/5000000000 : ℝ)] ![(2078761241789/6250000000000 : ℝ), (4531428321729/12500000000000 : ℝ), (15244196777353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258055271/10000000000 : ℝ)|^4563 ≤ (2078761241789/6250000000000 : ℝ)^3539
        have hw : |(4258055271/10000000000 : ℝ)|=(4258055271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4552171483/10000000000 : ℝ)|^4563 ≤ (4531428321729/12500000000000 : ℝ)^3539
        have hw : |(4552171483/10000000000 : ℝ)|=(4552171483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1990086047/5000000000 : ℝ)|^4563 ≤ (15244196777353/50000000000000 : ℝ)^3539
        have hw : |(1990086047/5000000000 : ℝ)|=(1990086047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1533_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (566/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8629/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (331/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7961/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (566/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8629/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (566/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8629/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (566/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8629/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (566/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8629/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (566/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8629/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (566/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8629/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8629/100000 : ℝ) ^ (4561/1024 : ℝ) ≤ (455616948502141/25000000000000000000 : ℝ) := by
    have hpowers : (8629/100000 : ℝ)^4561 ≤ (455616948502141/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8629 : ℕ)^4561*25000000000000000000^1024 ≤ 455616948502141^1024*100000^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8629 100000 455616948502141 25000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8629/100000 : ℝ)) (X := (455616948502141/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (566/3125 : ℝ) ^ (4561/1024 : ℝ) ≤ (24767206747748709/50000000000000000000 : ℝ) := by
    have hpowers : (566/3125 : ℝ)^4561 ≤ (24767206747748709/50000000000000000000 : ℝ)^1024 := by
      have hnat : (566 : ℕ)^4561*50000000000000000000^1024 ≤ 24767206747748709^1024*3125^4561 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        566 3125 24767206747748709 50000000000000000000 4561 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (566/3125 : ℝ)) (X := (24767206747748709/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500455616948502141/12500000000000000000 : ℝ) ≤ (2500020458020681/2500000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (12500455616948502141/12500000000000000000 : ℝ)^1024 ≤ (2500020458020681/2500000000000000 : ℝ)^4561 := by
      have hnat : (12500455616948502141 : ℕ)^1024*2500000000000000^4561 ≤ 2500020458020681^4561*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500455616948502141 12500000000000000000 2500020458020681 2500000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500020458020681/2500000000000000 : ℝ)) (X := (12500455616948502141/12500000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025678440644752991/50000000000000000000 : ℝ) ≤ (2000230558988461/2000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (50025678440644752991/50000000000000000000 : ℝ)^1024 ≤ (2000230558988461/2000000000000000 : ℝ)^4561 := by
      have hnat : (50025678440644752991 : ℕ)^1024*2000000000000000^4561 ≤ 2000230558988461^4561*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025678440644752991 50000000000000000000 2000230558988461 2000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000230558988461/2000000000000000 : ℝ)) (X := (50025678440644752991/50000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25024767206747748709/25000000000000000000 : ℝ) ≤ (5001111878900943/5000000000000000 : ℝ) ^ (4561/1024 : ℝ) := by
    have hpowers : (25024767206747748709/25000000000000000000 : ℝ)^1024 ≤ (5001111878900943/5000000000000000 : ℝ)^4561 := by
      have hnat : (25024767206747748709 : ℕ)^1024*5000000000000000^4561 ≤ 5001111878900943^4561*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024767206747748709 25000000000000000000 5001111878900943 5000000000000000 1024 4561 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001111878900943/5000000000000000 : ℝ)) (X := (25024767206747748709/25000000000000000000 : ℝ)) (by norm_num) 4561 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(455616948502141/25000000000000000000 : ℝ) ≤ ((47406146668304911397/47415000000000000000 : ℝ)+2*(1070962859581/948300000000000 : ℝ)*(8629/100000 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (47406146668304911397/47415000000000000000 : ℝ)+2*(1070962859581/948300000000000 : ℝ)*(8629/100000 : ℝ)=(2500020458020681/2500000000000000 : ℝ) by norm_num, show 1+2*(455616948502141/25000000000000000000 : ℝ)=(12500455616948502141/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24767206747748709/50000000000000000000 : ℝ)+(455616948502141/25000000000000000000 : ℝ) ≤ ((47406146668304911397/47415000000000000000 : ℝ)+(1070962859581/948300000000000 : ℝ)*((566/3125 : ℝ)+(8629/100000 : ℝ)))^(4561/1024 : ℝ) := by
    rw [show (47406146668304911397/47415000000000000000 : ℝ)+(1070962859581/948300000000000 : ℝ)*((566/3125 : ℝ)+(8629/100000 : ℝ))=(2000230558988461/2000000000000000 : ℝ) by norm_num, show 1+(24767206747748709/50000000000000000000 : ℝ)+(455616948502141/25000000000000000000 : ℝ)=(50025678440644752991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24767206747748709/50000000000000000000 : ℝ) ≤ ((47406146668304911397/47415000000000000000 : ℝ)+2*(1070962859581/948300000000000 : ℝ)*(566/3125 : ℝ))^(4561/1024 : ℝ) := by
    rw [show (47406146668304911397/47415000000000000000 : ℝ)+2*(1070962859581/948300000000000 : ℝ)*(566/3125 : ℝ)=(5001111878900943/5000000000000000 : ℝ) by norm_num, show 1+2*(24767206747748709/50000000000000000000 : ℝ)=(25024767206747748709/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47406146668304911397/47415000000000000000 : ℝ)*(X 1 0+X 2 0)+(1070962859581/948300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (8629/100000 : ℝ)) (hi := (566/3125 : ℝ)) (c := (47406146668304911397/47415000000000000000 : ℝ)) (alpha := (1070962859581/948300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47406146668304911397/47415000000000000000 : ℝ)*(X 0 1+X 2 1)+(1070962859581/948300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (8629/100000 : ℝ)) (hi := (566/3125 : ℝ)) (c := (47406146668304911397/47415000000000000000 : ℝ)) (alpha := (1070962859581/948300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47406146668304911397/47415000000000000000 : ℝ)*(X 0 2+X 1 2)+(1070962859581/948300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4561/1024 : ℝ)) (lo := (8629/100000 : ℝ)) (hi := (566/3125 : ℝ)) (c := (47406146668304911397/47415000000000000000 : ℝ)) (alpha := (1070962859581/948300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1834130921/10000000000 : ℝ)*X 0 0+(1090298717/2000000000 : ℝ)*X 0 1+(5199826459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338971131/2500000000 : ℝ)*X 1 0+(-1963531527/10000000000 : ℝ)*X 1 1+(1299956701/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071177041/2000000000 : ℝ)*X 2 0+(5199826411/10000000000 : ℝ)*X 2 1+(-981765569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((85158937/200000000 : ℝ)*X 0 0+(994147461/2500000000 : ℝ)*X 0 1+(2277861357/5000000000 : ℝ)*X 0 2+(85158937/200000000 : ℝ)*X 1 0+(994147461/2500000000 : ℝ)*X 1 1+(2277861357/5000000000 : ℝ)*X 1 2+(85158937/200000000 : ℝ)*X 2 0+(994147461/2500000000 : ℝ)*X 2 1+(2277861357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-458544419/2500000000 : ℝ)*X 0 0+(650171161/1250000000 : ℝ)*X 0 1+(5449937467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057921217/2000000000 : ℝ)*X 1 0+(-1713420363/10000000000 : ℝ)*X 1 1+(1089987463/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264480287/500000000 : ℝ)*X 2 0+(2724968749/5000000000 : ℝ)*X 2 1+(-1713420587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4258055271/10000000000 : ℝ)*X 0 0+(4552171483/10000000000 : ℝ)*X 0 1+(1990086047/5000000000 : ℝ)*X 0 2+(4258055271/10000000000 : ℝ)*X 1 0+(4552171483/10000000000 : ℝ)*X 1 1+(1990086047/5000000000 : ℝ)*X 1 2+(4258055271/10000000000 : ℝ)*X 2 0+(4552171483/10000000000 : ℝ)*X 2 1+(1990086047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1533_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (729866250325658227171324001/395125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (340527593/50000000000000 : ℝ)*(base19) + (102439331/12500000000000 : ℝ)*(base23) + (29530529/100000000000000 : ℝ)*(upper3) + (1571519/800000000000 : ℝ)*(upper4) + (92700781/50000000000000 : ℝ)*(upper5) + (1425065491785733/50000000000000 : ℝ)*(major0) + (1425065491785733/50000000000000 : ℝ)*(major1) + (1425065491785733/50000000000000 : ℝ)*(major2) + (993377520299129/25000000000000 : ℝ)*(sp0) + (1986763385703053/50000000000000 : ℝ)*(sp1) + (993381658236661/25000000000000 : ℝ)*(sp2) + (863363344108387/50000000000000 : ℝ)*(sp3) + (17371264777/100000000000000 : ℝ)*(sp4) + (3882446127/50000000000000 : ℝ)*(sp7) + (431683613277257/25000000000000 : ℝ)*(f.failure) + (993381863115323/25000000000000 : ℝ)*(f.sum) + (884943853073/370429687500000000000000000 : ℝ)*base66 + (14828904974543150999/2370750000000000000000000000000000 : ℝ)*base68 + (21284757458693900999/2370750000000000000000000000000000 : ℝ)*base70 + (21334199599301150999/2370750000000000000000000000000000 : ℝ)*base72 + (23891123466103/23707500000000000000000000000 : ℝ)*base73 + (23468012335145349001/2370750000000000000000000000000000 : ℝ)*base75 + (14955693111278150999/2370750000000000000000000000000000 : ℝ)*base78 + (29450313369660849001/2370750000000000000000000000000000 : ℝ)*base79 + (32553095662573/23707500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8014603/2500000000000000000000 : ℝ)*base90 + (8014603/2500000000000000000000 : ℝ)*base92 + (8014603/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (950764391249749751540606061/98781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2015722231/100000000000000 : ℝ)*(base19) + (1685059177/100000000000000 : ℝ)*(base23) + (6494333/100000000000000 : ℝ)*(upper2) + (18714149/12500000000000 : ℝ)*(upper3) + (267928281/100000000000000 : ℝ)*(upper5) + (721411824003213/25000000000000 : ℝ)*(major0) + (721411824003213/25000000000000 : ℝ)*(major1) + (721411824003213/25000000000000 : ℝ)*(major2) + (14119814671/50000000000000 : ℝ)*(sp1) + (4362156491/20000000000000 : ℝ)*(sp2) + (2011521238529947/50000000000000 : ℝ)*(sp4) + (2011506110854161/50000000000000 : ℝ)*(sp5) + (2011509490609131/50000000000000 : ℝ)*(sp6) + (437062948533551/25000000000000 : ℝ)*(sp7) + (437062948533551/25000000000000 : ℝ)*(f.failure) + (2011521238529947/50000000000000 : ℝ)*(f.sum) + (758494416303/493906250000000000000000000 : ℝ)*base66 + (5760152777081843813/395125000000000000000000000000000 : ℝ)*base68 + (14080824309406187/395125000000000000000000000000000 : ℝ)*base69 + (2461725084974093813/395125000000000000000000000000000 : ℝ)*base72 + (3707181991041/987812500000000000000000000 : ℝ)*base74 + (4078098369928093813/395125000000000000000000000000000 : ℝ)*base76 + (729362575336218813/395125000000000000000000000000000 : ℝ)*base78 + (6033765779637968813/395125000000000000000000000000000 : ℝ)*base80 + (9223000273361/3951250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (13713571/2500000000000000000000 : ℝ)*base89 + (13713571/2500000000000000000000 : ℝ)*base91 + (13713571/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1533_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (566/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8629/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (331/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7961/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1533_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1533_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (331/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7961/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1533_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1533_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1533_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4561/1024 : ℝ) ≤ p) (hpb : p ≤ (4563/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165059021/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (331/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7961/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1533_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
