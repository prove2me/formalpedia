-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1176_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:47:40.978083+00:00
-- url     : https://prove2.me/submissions/1257c251-8818-4e18-b4a3-52cde199630b

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
theorem support_rectangle_w1176_s0_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1881096309/10000000000 : ℝ)*x 0 + (3023252597/5000000000 : ℝ)*x 1 + (478475727/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1881096309/10000000000 : ℝ)^8369 ≤ (10947643953799/100000000000000 : ℝ)^6321 := by
    have hnat : (1881096309 : ℕ)^8369*100000000000000^6321 ≤ 10947643953799^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881096309 10000000000 10947643953799 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3023252597/5000000000 : ℝ)^8369 ≤ (5137028840293/10000000000000 : ℝ)^6321 := by
    have hnat : (3023252597 : ℕ)^8369*10000000000000^6321 ≤ 5137028840293^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3023252597 5000000000 5137028840293 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478475727/1000000000 : ℝ)^8369 ≤ (37682067633461/100000000000000 : ℝ)^6321 := by
    have hnat : (478475727 : ℕ)^8369*100000000000000^6321 ≤ 37682067633461^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478475727 1000000000 37682067633461 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1881096309/10000000000 : ℝ), (3023252597/5000000000 : ℝ), (478475727/1000000000 : ℝ)] ![(10947643953799/100000000000000 : ℝ), (5137028840293/10000000000000 : ℝ), (37682067633461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1881096309/10000000000 : ℝ)|^8369 ≤ (10947643953799/100000000000000 : ℝ)^6321
        have hw : |(-1881096309/10000000000 : ℝ)|=(1881096309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3023252597/5000000000 : ℝ)|^8369 ≤ (5137028840293/10000000000000 : ℝ)^6321
        have hw : |(3023252597/5000000000 : ℝ)|=(3023252597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478475727/1000000000 : ℝ)|^8369 ≤ (37682067633461/100000000000000 : ℝ)^6321
        have hw : |(478475727/1000000000 : ℝ)|=(478475727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s0_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5514878113/10000000000 : ℝ)*x 0 + (-2604235259/10000000000 : ℝ)*x 1 + (1196189313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514878113/10000000000 : ℝ)^8369 ≤ (45477200188591/100000000000000 : ℝ)^6321 := by
    have hnat : (5514878113 : ℕ)^8369*100000000000000^6321 ≤ 45477200188591^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514878113 10000000000 45477200188591 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2604235259/10000000000 : ℝ)^8369 ≤ (8420366178521/50000000000000 : ℝ)^6321 := by
    have hnat : (2604235259 : ℕ)^8369*50000000000000^6321 ≤ 8420366178521^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604235259 10000000000 8420366178521 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196189313/2500000000 : ℝ)^8369 ≤ (37682067445773/100000000000000 : ℝ)^6321 := by
    have hnat : (1196189313 : ℕ)^8369*100000000000000^6321 ≤ 37682067445773^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196189313 2500000000 37682067445773 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514878113/10000000000 : ℝ), (-2604235259/10000000000 : ℝ), (1196189313/2500000000 : ℝ)] ![(45477200188591/100000000000000 : ℝ), (8420366178521/50000000000000 : ℝ), (37682067445773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514878113/10000000000 : ℝ)|^8369 ≤ (45477200188591/100000000000000 : ℝ)^6321
        have hw : |(5514878113/10000000000 : ℝ)|=(5514878113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2604235259/10000000000 : ℝ)|^8369 ≤ (8420366178521/50000000000000 : ℝ)^6321
        have hw : |(-2604235259/10000000000 : ℝ)|=(2604235259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196189313/2500000000 : ℝ)|^8369 ≤ (37682067445773/100000000000000 : ℝ)^6321
        have hw : |(1196189313/2500000000 : ℝ)|=(1196189313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s0_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757439063/5000000000 : ℝ)*x 0 + (4784757247/10000000000 : ℝ)*x 1 + (-2604235247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757439063/5000000000 : ℝ)^8369 ≤ (22738600165263/50000000000000 : ℝ)^6321 := by
    have hnat : (2757439063 : ℕ)^8369*50000000000000^6321 ≤ 22738600165263^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757439063 5000000000 22738600165263 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4784757247/10000000000 : ℝ)^8369 ≤ (18841033696819/50000000000000 : ℝ)^6321 := by
    have hnat : (4784757247 : ℕ)^8369*50000000000000^6321 ≤ 18841033696819^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4784757247 10000000000 18841033696819 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2604235247/10000000000 : ℝ)^8369 ≤ (168407322543/1000000000000 : ℝ)^6321 := by
    have hnat : (2604235247 : ℕ)^8369*1000000000000^6321 ≤ 168407322543^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604235247 10000000000 168407322543 1000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757439063/5000000000 : ℝ), (4784757247/10000000000 : ℝ), (-2604235247/10000000000 : ℝ)] ![(22738600165263/50000000000000 : ℝ), (18841033696819/50000000000000 : ℝ), (168407322543/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757439063/5000000000 : ℝ)|^8369 ≤ (22738600165263/50000000000000 : ℝ)^6321
        have hw : |(2757439063/5000000000 : ℝ)|=(2757439063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4784757247/10000000000 : ℝ)|^8369 ≤ (18841033696819/50000000000000 : ℝ)^6321
        have hw : |(4784757247/10000000000 : ℝ)|=(4784757247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2604235247/10000000000 : ℝ)|^8369 ≤ (168407322543/1000000000000 : ℝ)^6321
        have hw : |(-2604235247/10000000000 : ℝ)|=(2604235247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s0_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2099127457/5000000000 : ℝ)*x 0 + (3119555517/10000000000 : ℝ)*x 1 + (5646521737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099127457/5000000000 : ℝ)^8369 ≤ (15845769736583/50000000000000 : ℝ)^6321 := by
    have hnat : (2099127457 : ℕ)^8369*50000000000000^6321 ≤ 15845769736583^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099127457 5000000000 15845769736583 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3119555517/10000000000 : ℝ)^8369 ≤ (2673554816831/12500000000000 : ℝ)^6321 := by
    have hnat : (3119555517 : ℕ)^8369*12500000000000^6321 ≤ 2673554816831^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119555517 10000000000 2673554816831 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5646521737/10000000000 : ℝ)^8369 ≤ (5865002746761/12500000000000 : ℝ)^6321 := by
    have hnat : (5646521737 : ℕ)^8369*12500000000000^6321 ≤ 5865002746761^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646521737 10000000000 5865002746761 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099127457/5000000000 : ℝ), (3119555517/10000000000 : ℝ), (5646521737/10000000000 : ℝ)] ![(15845769736583/50000000000000 : ℝ), (2673554816831/12500000000000 : ℝ), (5865002746761/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099127457/5000000000 : ℝ)|^8369 ≤ (15845769736583/50000000000000 : ℝ)^6321
        have hw : |(2099127457/5000000000 : ℝ)|=(2099127457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3119555517/10000000000 : ℝ)|^8369 ≤ (2673554816831/12500000000000 : ℝ)^6321
        have hw : |(3119555517/10000000000 : ℝ)|=(3119555517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5646521737/10000000000 : ℝ)|^8369 ≤ (5865002746761/12500000000000 : ℝ)^6321
        have hw : |(5646521737/10000000000 : ℝ)|=(5646521737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s0_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-943071307/5000000000 : ℝ)*x 0 + (4817288941/10000000000 : ℝ)*x 1 + (60128273/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943071307/5000000000 : ℝ)^8369 ≤ (343329526237/3125000000000 : ℝ)^6321 := by
    have hnat : (943071307 : ℕ)^8369*3125000000000^6321 ≤ 343329526237^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943071307 5000000000 343329526237 3125000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4817288941/10000000000 : ℝ)^8369 ≤ (38021650928983/100000000000000 : ℝ)^6321 := by
    have hnat : (4817288941 : ℕ)^8369*100000000000000^6321 ≤ 38021650928983^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817288941 10000000000 38021650928983 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60128273/100000000 : ℝ)^8369 ≤ (10198360843213/20000000000000 : ℝ)^6321 := by
    have hnat : (60128273 : ℕ)^8369*20000000000000^6321 ≤ 10198360843213^6321*100000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60128273 100000000 10198360843213 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943071307/5000000000 : ℝ), (4817288941/10000000000 : ℝ), (60128273/100000000 : ℝ)] ![(343329526237/3125000000000 : ℝ), (38021650928983/100000000000000 : ℝ), (10198360843213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943071307/5000000000 : ℝ)|^8369 ≤ (343329526237/3125000000000 : ℝ)^6321
        have hw : |(-943071307/5000000000 : ℝ)|=(943071307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4817288941/10000000000 : ℝ)|^8369 ≤ (38021650928983/100000000000000 : ℝ)^6321
        have hw : |(4817288941/10000000000 : ℝ)|=(4817288941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60128273/100000000 : ℝ)|^8369 ≤ (10198360843213/20000000000000 : ℝ)^6321
        have hw : |(60128273/100000000 : ℝ)|=(60128273/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s0_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585935339/5000000000 : ℝ)*x 0 + (-43005169/312500000 : ℝ)*x 1 + (6012827043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585935339/5000000000 : ℝ)^8369 ≤ (417705004827/1000000000000 : ℝ)^6321 := by
    have hnat : (2585935339 : ℕ)^8369*1000000000000^6321 ≤ 417705004827^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585935339 5000000000 417705004827 1000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43005169/312500000 : ℝ)^8369 ≤ (7237698177573/100000000000000 : ℝ)^6321 := by
    have hnat : (43005169 : ℕ)^8369*100000000000000^6321 ≤ 7237698177573^6321*312500000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43005169 312500000 7237698177573 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6012827043/10000000000 : ℝ)^8369 ≤ (25495900665211/50000000000000 : ℝ)^6321 := by
    have hnat : (6012827043 : ℕ)^8369*50000000000000^6321 ≤ 25495900665211^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012827043 10000000000 25495900665211 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585935339/5000000000 : ℝ), (-43005169/312500000 : ℝ), (6012827043/10000000000 : ℝ)] ![(417705004827/1000000000000 : ℝ), (7237698177573/100000000000000 : ℝ), (25495900665211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585935339/5000000000 : ℝ)|^8369 ≤ (417705004827/1000000000000 : ℝ)^6321
        have hw : |(2585935339/5000000000 : ℝ)|=(2585935339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43005169/312500000 : ℝ)|^8369 ≤ (7237698177573/100000000000000 : ℝ)^6321
        have hw : |(-43005169/312500000 : ℝ)|=(43005169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6012827043/10000000000 : ℝ)|^8369 ≤ (25495900665211/50000000000000 : ℝ)^6321
        have hw : |(6012827043/10000000000 : ℝ)|=(6012827043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s0_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171870633/10000000000 : ℝ)*x 0 + (6012827167/10000000000 : ℝ)*x 1 + (-344041319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171870633/10000000000 : ℝ)^8369 ≤ (41770500001503/100000000000000 : ℝ)^6321 := by
    have hnat : (5171870633 : ℕ)^8369*100000000000000^6321 ≤ 41770500001503^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171870633 10000000000 41770500001503 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6012827167/10000000000 : ℝ)^8369 ≤ (50991802722717/100000000000000 : ℝ)^6321 := by
    have hnat : (6012827167 : ℕ)^8369*100000000000000^6321 ≤ 50991802722717^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012827167 10000000000 50991802722717 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344041319/2500000000 : ℝ)^8369 ≤ (1809424314603/25000000000000 : ℝ)^6321 := by
    have hnat : (344041319 : ℕ)^8369*25000000000000^6321 ≤ 1809424314603^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344041319 2500000000 1809424314603 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171870633/10000000000 : ℝ), (6012827167/10000000000 : ℝ), (-344041319/2500000000 : ℝ)] ![(41770500001503/100000000000000 : ℝ), (50991802722717/100000000000000 : ℝ), (1809424314603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171870633/10000000000 : ℝ)|^8369 ≤ (41770500001503/100000000000000 : ℝ)^6321
        have hw : |(5171870633/10000000000 : ℝ)|=(5171870633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6012827167/10000000000 : ℝ)|^8369 ≤ (50991802722717/100000000000000 : ℝ)^6321
        have hw : |(6012827167/10000000000 : ℝ)|=(6012827167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-344041319/2500000000 : ℝ)|^8369 ≤ (1809424314603/25000000000000 : ℝ)^6321
        have hw : |(-344041319/2500000000 : ℝ)|=(344041319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s0_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1052090377/2500000000 : ℝ)*x 0 + (1116273709/2000000000 : ℝ)*x 1 + (796751057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052090377/2500000000 : ℝ)^8369 ≤ (31792589485997/100000000000000 : ℝ)^6321 := by
    have hnat : (1052090377 : ℕ)^8369*100000000000000^6321 ≤ 31792589485997^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052090377 2500000000 31792589485997 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116273709/2000000000 : ℝ)^8369 ≤ (5640205193/12207031250 : ℝ)^6321 := by
    have hnat : (1116273709 : ℕ)^8369*12207031250^6321 ≤ 5640205193^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116273709 2000000000 5640205193 12207031250 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796751057/2500000000 : ℝ)^8369 ≤ (22002849547823/100000000000000 : ℝ)^6321 := by
    have hnat : (796751057 : ℕ)^8369*100000000000000^6321 ≤ 22002849547823^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796751057 2500000000 22002849547823 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052090377/2500000000 : ℝ), (1116273709/2000000000 : ℝ), (796751057/2500000000 : ℝ)] ![(31792589485997/100000000000000 : ℝ), (5640205193/12207031250 : ℝ), (22002849547823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052090377/2500000000 : ℝ)|^8369 ≤ (31792589485997/100000000000000 : ℝ)^6321
        have hw : |(1052090377/2500000000 : ℝ)|=(1052090377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1116273709/2000000000 : ℝ)|^8369 ≤ (5640205193/12207031250 : ℝ)^6321
        have hw : |(1116273709/2000000000 : ℝ)|=(1116273709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796751057/2500000000 : ℝ)|^8369 ≤ (22002849547823/100000000000000 : ℝ)^6321
        have hw : |(796751057/2500000000 : ℝ)|=(796751057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (553/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5537/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (523/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^523 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^523*1^128 ≤ 0^128*1^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (523/128 : ℝ) ≤ (2366148490477459697/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^523 ≤ (2366148490477459697/100000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^523*100000000000000000000^128 ≤ 2366148490477459697^128*5^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2366148490477459697 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2366148490477459697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^523 := by
      have hnat : (1 : ℕ)^128*1^523 ≤ 1^523*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (102366148490477459697/100000000000000000000 : ℝ) ≤ (502869958648611/500000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (102366148490477459697/100000000000000000000 : ℝ)^128 ≤ (502869958648611/500000000000000 : ℝ)^523 := by
      have hnat : (102366148490477459697 : ℕ)^128*500000000000000^523 ≤ 502869958648611^523*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102366148490477459697 100000000000000000000 502869958648611 500000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502869958648611/500000000000000 : ℝ)) (X := (102366148490477459697/100000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (52366148490477459697/50000000000000000000 : ℝ) ≤ (252869958648611/250000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (52366148490477459697/50000000000000000000 : ℝ)^128 ≤ (252869958648611/250000000000000 : ℝ)^523 := by
      have hnat : (52366148490477459697 : ℕ)^128*250000000000000^523 ≤ 252869958648611^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52366148490477459697 50000000000000000000 252869958648611 250000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252869958648611/250000000000000 : ℝ)) (X := (52366148490477459697/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2869958648611/200000000000000 : ℝ)*(0 : ℝ))^(523/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(2869958648611/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2366148490477459697/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2869958648611/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(523/128 : ℝ) := by
    rw [show (1 : ℝ)+(2869958648611/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(502869958648611/500000000000000 : ℝ) by norm_num, show 1+(2366148490477459697/100000000000000000000 : ℝ)+(0 : ℝ)=(102366148490477459697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2366148490477459697/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2869958648611/200000000000000 : ℝ)*(2/5 : ℝ))^(523/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(2869958648611/200000000000000 : ℝ)*(2/5 : ℝ)=(252869958648611/250000000000000 : ℝ) by norm_num, show 1+2*(2366148490477459697/100000000000000000000 : ℝ)=(52366148490477459697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2869958648611/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2869958648611/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2869958648611/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2869958648611/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2869958648611/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2869958648611/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1881096309/10000000000 : ℝ)*X 0 0+(3023252597/5000000000 : ℝ)*X 0 1+(478475727/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5514878113/10000000000 : ℝ)*X 1 0+(-2604235259/10000000000 : ℝ)*X 1 1+(1196189313/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757439063/5000000000 : ℝ)*X 2 0+(4784757247/10000000000 : ℝ)*X 2 1+(-2604235247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2099127457/5000000000 : ℝ)*X 0 0+(3119555517/10000000000 : ℝ)*X 0 1+(5646521737/10000000000 : ℝ)*X 0 2+(2099127457/5000000000 : ℝ)*X 1 0+(3119555517/10000000000 : ℝ)*X 1 1+(5646521737/10000000000 : ℝ)*X 1 2+(2099127457/5000000000 : ℝ)*X 2 0+(3119555517/10000000000 : ℝ)*X 2 1+(5646521737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-943071307/5000000000 : ℝ)*X 0 0+(4817288941/10000000000 : ℝ)*X 0 1+(60128273/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585935339/5000000000 : ℝ)*X 1 0+(-43005169/312500000 : ℝ)*X 1 1+(6012827043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171870633/10000000000 : ℝ)*X 2 0+(6012827167/10000000000 : ℝ)*X 2 1+(-344041319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052090377/2500000000 : ℝ)*X 0 0+(1116273709/2000000000 : ℝ)*X 0 1+(796751057/2500000000 : ℝ)*X 0 2+(1052090377/2500000000 : ℝ)*X 1 0+(1116273709/2000000000 : ℝ)*X 1 1+(796751057/2500000000 : ℝ)*X 1 2+(1052090377/2500000000 : ℝ)*X 2 0+(1116273709/2000000000 : ℝ)*X 2 1+(796751057/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112690273217108997/50000000000000000000000 : ℝ) := by norm_num
    linear_combination (24768689/100000000000000 : ℝ)*(base1) + (275520711/50000000000000 : ℝ)*(base19) + (257164909/50000000000000 : ℝ)*(base23) + (38579859/100000000000000 : ℝ)*(base24) + (15655011/12500000000000 : ℝ)*(upper3) + (297071859594639/50000000000000 : ℝ)*(major0) + (297071859594639/50000000000000 : ℝ)*(major1) + (297071859594639/50000000000000 : ℝ)*(major2) + (396276586853573/50000000000000 : ℝ)*(sp0) + (792553810072011/100000000000000 : ℝ)*(sp1) + (198138452050939/25000000000000 : ℝ)*(sp2) + (79146402561401/20000000000000 : ℝ)*(sp3) + (9470117/781250000000 : ℝ)*(sp4) + (482281289/50000000000000 : ℝ)*(sp7) + (12366656316821/3125000000000 : ℝ)*(f.failure) + (792554361113433/100000000000000 : ℝ)*(f.sum) + (7830143683571/5000000000000000000000000000 : ℝ)*base66 + (20849077046429/10000000000000000000000000000 : ℝ)*base67 + (5688263506429/10000000000000000000000000000 : ℝ)*base69 + (12827546026429/10000000000000000000000000000 : ℝ)*base71 + (9431648333571/5000000000000000000000000000 : ℝ)*base74 + (30384487986429/10000000000000000000000000000 : ℝ)*base75 + (3851085896429/10000000000000000000000000000 : ℝ)*base77 + (14769447126429/10000000000000000000000000000 : ℝ)*base79 + (19331098288571/5000000000000000000000000000 : ℝ)*base82 + (1790741/312500000000000000000 : ℝ)*base89 + (1790741/312500000000000000000 : ℝ)*base91 + (1790741/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4247483856221094688827/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21596071/50000000000000 : ℝ)*(base1) + (431621387/50000000000000 : ℝ)*(base19) + (274447/32000000000 : ℝ)*(base23) + (8651473/10000000000000 : ℝ)*(upper3) + (21363923/20000000000000 : ℝ)*(upper5) + (78380676929769/12500000000000 : ℝ)*(major0) + (78380676929769/12500000000000 : ℝ)*(major1) + (78380676929769/12500000000000 : ℝ)*(major2) + (1711692719/100000000000000 : ℝ)*(sp1) + (434263091/25000000000000 : ℝ)*(sp2) + (418221692870603/50000000000000 : ℝ)*(sp4) + (209110191903393/25000000000000 : ℝ)*(sp5) + (418220373924913/50000000000000 : ℝ)*(sp6) + (83529466373771/20000000000000 : ℝ)*(sp7) + (104411843765249/25000000000000 : ℝ)*(f.failure) + (167288668509813/20000000000000 : ℝ)*(f.sum) + (2868304669141/1250000000000000000000000000 : ℝ)*base66 + (19938874348359/2500000000000000000000000000 : ℝ)*base67 + (10271810449141/2500000000000000000000000000 : ℝ)*base70 + (4368210393359/2500000000000000000000000000 : ℝ)*base71 + (3384959678359/1250000000000000000000000000 : ℝ)*base73 + (11658190409141/2500000000000000000000000000 : ℝ)*base76 + (199338745859/2500000000000000000000000000 : ℝ)*base77 + (2372880661641/2500000000000000000000000000 : ℝ)*base80 + (6787707419141/1250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (9192271/2500000000000000000000 : ℝ)*base90 + (9192271/2500000000000000000000 : ℝ)*base92 + (9192271/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1176_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (553/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5537/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1176_s1_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083300853/10000000000 : ℝ)*x 0 + (1423127139/2500000000 : ℝ)*x 1 + (500931357/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083300853/10000000000 : ℝ)^8369 ≤ (3133055417513/25000000000000 : ℝ)^6321 := by
    have hnat : (2083300853 : ℕ)^8369*25000000000000^6321 ≤ 3133055417513^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083300853 10000000000 3133055417513 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423127139/2500000000 : ℝ)^8369 ≤ (23713313748673/50000000000000 : ℝ)^6321 := by
    have hnat : (1423127139 : ℕ)^8369*50000000000000^6321 ≤ 23713313748673^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423127139 2500000000 23713313748673 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500931357/1000000000 : ℝ)^8369 ≤ (40041150813149/100000000000000 : ℝ)^6321 := by
    have hnat : (500931357 : ℕ)^8369*100000000000000^6321 ≤ 40041150813149^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500931357 1000000000 40041150813149 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083300853/10000000000 : ℝ), (1423127139/2500000000 : ℝ), (500931357/1000000000 : ℝ)] ![(3133055417513/25000000000000 : ℝ), (23713313748673/50000000000000 : ℝ), (40041150813149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083300853/10000000000 : ℝ)|^8369 ≤ (3133055417513/25000000000000 : ℝ)^6321
        have hw : |(-2083300853/10000000000 : ℝ)|=(2083300853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1423127139/2500000000 : ℝ)|^8369 ≤ (23713313748673/50000000000000 : ℝ)^6321
        have hw : |(1423127139/2500000000 : ℝ)|=(1423127139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500931357/1000000000 : ℝ)|^8369 ≤ (40041150813149/100000000000000 : ℝ)^6321
        have hw : |(500931357/1000000000 : ℝ)|=(500931357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s1_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541725633/1000000000 : ℝ)*x 0 + (-490271531/2000000000 : ℝ)*x 1 + (250465631/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541725633/1000000000 : ℝ)^8369 ≤ (44414428186891/100000000000000 : ℝ)^6321 := by
    have hnat : (541725633 : ℕ)^8369*100000000000000^6321 ≤ 44414428186891^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541725633 1000000000 44414428186891 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490271531/2000000000 : ℝ)^8369 ≤ (15544431035403/100000000000000 : ℝ)^6321 := by
    have hnat : (490271531 : ℕ)^8369*100000000000000^6321 ≤ 15544431035403^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490271531 2000000000 15544431035403 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250465631/500000000 : ℝ)^8369 ≤ (4004114075913/10000000000000 : ℝ)^6321 := by
    have hnat : (250465631 : ℕ)^8369*10000000000000^6321 ≤ 4004114075913^6321*500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250465631 500000000 4004114075913 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541725633/1000000000 : ℝ), (-490271531/2000000000 : ℝ), (250465631/500000000 : ℝ)] ![(44414428186891/100000000000000 : ℝ), (15544431035403/100000000000000 : ℝ), (4004114075913/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541725633/1000000000 : ℝ)|^8369 ≤ (44414428186891/100000000000000 : ℝ)^6321
        have hw : |(541725633/1000000000 : ℝ)|=(541725633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-490271531/2000000000 : ℝ)|^8369 ≤ (15544431035403/100000000000000 : ℝ)^6321
        have hw : |(-490271531/2000000000 : ℝ)|=(490271531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(250465631/500000000 : ℝ)|^8369 ≤ (4004114075913/10000000000000 : ℝ)^6321
        have hw : |(250465631/500000000 : ℝ)|=(250465631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s1_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417258431/10000000000 : ℝ)*x 0 + (1001862127/2000000000 : ℝ)*x 1 + (-2451357441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417258431/10000000000 : ℝ)^8369 ≤ (22207225496693/50000000000000 : ℝ)^6321 := by
    have hnat : (5417258431 : ℕ)^8369*50000000000000^6321 ≤ 22207225496693^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417258431 10000000000 22207225496693 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001862127/2000000000 : ℝ)^8369 ≤ (10010279937881/25000000000000 : ℝ)^6321 := by
    have hnat : (1001862127 : ℕ)^8369*25000000000000^6321 ≤ 10010279937881^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001862127 2000000000 10010279937881 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2451357441/10000000000 : ℝ)^8369 ≤ (15544429238727/100000000000000 : ℝ)^6321 := by
    have hnat : (2451357441 : ℕ)^8369*100000000000000^6321 ≤ 15544429238727^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451357441 10000000000 15544429238727 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417258431/10000000000 : ℝ), (1001862127/2000000000 : ℝ), (-2451357441/10000000000 : ℝ)] ![(22207225496693/50000000000000 : ℝ), (10010279937881/25000000000000 : ℝ), (15544429238727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417258431/10000000000 : ℝ)|^8369 ≤ (22207225496693/50000000000000 : ℝ)^6321
        have hw : |(5417258431/10000000000 : ℝ)|=(5417258431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001862127/2000000000 : ℝ)|^8369 ≤ (10010279937881/25000000000000 : ℝ)^6321
        have hw : |(1001862127/2000000000 : ℝ)|=(1001862127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2451357441/10000000000 : ℝ)|^8369 ≤ (15544429238727/100000000000000 : ℝ)^6321
        have hw : |(-2451357441/10000000000 : ℝ)|=(2451357441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s1_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2157274573/5000000000 : ℝ)*x 0 + (3683399731/10000000000 : ℝ)*x 1 + (5051663071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157274573/5000000000 : ℝ)^8369 ≤ (16429514568567/50000000000000 : ℝ)^6321 := by
    have hnat : (2157274573 : ℕ)^8369*50000000000000^6321 ≤ 16429514568567^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157274573 5000000000 16429514568567 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3683399731/10000000000 : ℝ)^8369 ≤ (26651015053631/100000000000000 : ℝ)^6321 := by
    have hnat : (3683399731 : ℕ)^8369*100000000000000^6321 ≤ 26651015053631^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3683399731 10000000000 26651015053631 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5051663071/10000000000 : ℝ)^8369 ≤ (40489955795867/100000000000000 : ℝ)^6321 := by
    have hnat : (5051663071 : ℕ)^8369*100000000000000^6321 ≤ 40489955795867^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051663071 10000000000 40489955795867 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157274573/5000000000 : ℝ), (3683399731/10000000000 : ℝ), (5051663071/10000000000 : ℝ)] ![(16429514568567/50000000000000 : ℝ), (26651015053631/100000000000000 : ℝ), (40489955795867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157274573/5000000000 : ℝ)|^8369 ≤ (16429514568567/50000000000000 : ℝ)^6321
        have hw : |(2157274573/5000000000 : ℝ)|=(2157274573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3683399731/10000000000 : ℝ)|^8369 ≤ (26651015053631/100000000000000 : ℝ)^6321
        have hw : |(3683399731/10000000000 : ℝ)|=(3683399731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5051663071/10000000000 : ℝ)|^8369 ≤ (40489955795867/100000000000000 : ℝ)^6321
        have hw : |(5051663071/10000000000 : ℝ)|=(5051663071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s1_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-208406427/1000000000 : ℝ)*x 0 + (501852109/1000000000 : ℝ)*x 1 + (5683118271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208406427/1000000000 : ℝ)^8369 ≤ (2507660468079/20000000000000 : ℝ)^6321 := by
    have hnat : (208406427 : ℕ)^8369*20000000000000^6321 ≤ 2507660468079^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208406427 1000000000 2507660468079 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501852109/1000000000 : ℝ)^8369 ≤ (20069312321189/50000000000000 : ℝ)^6321 := by
    have hnat : (501852109 : ℕ)^8369*50000000000000^6321 ≤ 20069312321189^6321*1000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501852109 1000000000 20069312321189 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5683118271/10000000000 : ℝ)^8369 ≤ (9464614599003/20000000000000 : ℝ)^6321 := by
    have hnat : (5683118271 : ℕ)^8369*20000000000000^6321 ≤ 9464614599003^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683118271 10000000000 9464614599003 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208406427/1000000000 : ℝ), (501852109/1000000000 : ℝ), (5683118271/10000000000 : ℝ)] ![(2507660468079/20000000000000 : ℝ), (20069312321189/50000000000000 : ℝ), (9464614599003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208406427/1000000000 : ℝ)|^8369 ≤ (2507660468079/20000000000000 : ℝ)^6321
        have hw : |(-208406427/1000000000 : ℝ)|=(208406427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501852109/1000000000 : ℝ)|^8369 ≤ (20069312321189/50000000000000 : ℝ)^6321
        have hw : |(501852109/1000000000 : ℝ)|=(501852109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5683118271/10000000000 : ℝ)|^8369 ≤ (9464614599003/20000000000000 : ℝ)^6321
        have hw : |(5683118271/10000000000 : ℝ)|=(5683118271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s1_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5241801827/10000000000 : ℝ)*x 0 + (-888774779/5000000000 : ℝ)*x 1 + (5683120629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241801827/10000000000 : ℝ)^8369 ≤ (42519924929441/100000000000000 : ℝ)^6321 := by
    have hnat : (5241801827 : ℕ)^8369*100000000000000^6321 ≤ 42519924929441^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241801827 10000000000 42519924929441 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888774779/5000000000 : ℝ)^8369 ≤ (1015697606257/10000000000000 : ℝ)^6321 := by
    have hnat : (888774779 : ℕ)^8369*10000000000000^6321 ≤ 1015697606257^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888774779 5000000000 1015697606257 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5683120629/10000000000 : ℝ)^8369 ≤ (47323098991693/100000000000000 : ℝ)^6321 := by
    have hnat : (5683120629 : ℕ)^8369*100000000000000^6321 ≤ 47323098991693^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683120629 10000000000 47323098991693 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241801827/10000000000 : ℝ), (-888774779/5000000000 : ℝ), (5683120629/10000000000 : ℝ)] ![(42519924929441/100000000000000 : ℝ), (1015697606257/10000000000000 : ℝ), (47323098991693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241801827/10000000000 : ℝ)|^8369 ≤ (42519924929441/100000000000000 : ℝ)^6321
        have hw : |(5241801827/10000000000 : ℝ)|=(5241801827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-888774779/5000000000 : ℝ)|^8369 ≤ (1015697606257/10000000000000 : ℝ)^6321
        have hw : |(-888774779/5000000000 : ℝ)|=(888774779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5683120629/10000000000 : ℝ)|^8369 ≤ (47323098991693/100000000000000 : ℝ)^6321
        have hw : |(5683120629/10000000000 : ℝ)|=(5683120629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s1_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620900653/5000000000 : ℝ)*x 0 + (5683121709/10000000000 : ℝ)*x 1 + (-71101949/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620900653/5000000000 : ℝ)^8369 ≤ (42519919333961/100000000000000 : ℝ)^6321 := by
    have hnat : (2620900653 : ℕ)^8369*100000000000000^6321 ≤ 42519919333961^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620900653 5000000000 42519919333961 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5683121709/10000000000 : ℝ)^8369 ≤ (4732311089857/10000000000000 : ℝ)^6321 := by
    have hnat : (5683121709 : ℕ)^8369*10000000000000^6321 ≤ 4732311089857^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683121709 10000000000 4732311089857 10000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71101949/400000000 : ℝ)^8369 ≤ (2539242440153/25000000000000 : ℝ)^6321 := by
    have hnat : (71101949 : ℕ)^8369*25000000000000^6321 ≤ 2539242440153^6321*400000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71101949 400000000 2539242440153 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620900653/5000000000 : ℝ), (5683121709/10000000000 : ℝ), (-71101949/400000000 : ℝ)] ![(42519919333961/100000000000000 : ℝ), (4732311089857/10000000000000 : ℝ), (2539242440153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620900653/5000000000 : ℝ)|^8369 ≤ (42519919333961/100000000000000 : ℝ)^6321
        have hw : |(2620900653/5000000000 : ℝ)|=(2620900653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5683121709/10000000000 : ℝ)|^8369 ≤ (4732311089857/10000000000000 : ℝ)^6321
        have hw : |(5683121709/10000000000 : ℝ)|=(5683121709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71101949/400000000 : ℝ)|^8369 ≤ (2539242440153/25000000000000 : ℝ)^6321
        have hw : |(-71101949/400000000 : ℝ)|=(71101949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s1_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2158033349/5000000000 : ℝ)*x 0 + (2516613059/5000000000 : ℝ)*x 1 + (3702198517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158033349/5000000000 : ℝ)^8369 ≤ (16437166047977/50000000000000 : ℝ)^6321 := by
    have hnat : (2158033349 : ℕ)^8369*50000000000000^6321 ≤ 16437166047977^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158033349 5000000000 16437166047977 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516613059/5000000000 : ℝ)^8369 ≤ (40294417066387/100000000000000 : ℝ)^6321 := by
    have hnat : (2516613059 : ℕ)^8369*100000000000000^6321 ≤ 40294417066387^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516613059 5000000000 40294417066387 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3702198517/10000000000 : ℝ)^8369 ≤ (26831250826957/100000000000000 : ℝ)^6321 := by
    have hnat : (3702198517 : ℕ)^8369*100000000000000^6321 ≤ 26831250826957^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3702198517 10000000000 26831250826957 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158033349/5000000000 : ℝ), (2516613059/5000000000 : ℝ), (3702198517/10000000000 : ℝ)] ![(16437166047977/50000000000000 : ℝ), (40294417066387/100000000000000 : ℝ), (26831250826957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158033349/5000000000 : ℝ)|^8369 ≤ (16437166047977/50000000000000 : ℝ)^6321
        have hw : |(2158033349/5000000000 : ℝ)|=(2158033349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516613059/5000000000 : ℝ)|^8369 ≤ (40294417066387/100000000000000 : ℝ)^6321
        have hw : |(2516613059/5000000000 : ℝ)|=(2516613059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3702198517/10000000000 : ℝ)|^8369 ≤ (26831250826957/100000000000000 : ℝ)^6321
        have hw : |(3702198517/10000000000 : ℝ)|=(3702198517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5537/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2919/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4057/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5537/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5537/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5537/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5537/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5537/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5537/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (553/100000 : ℝ) ^ (523/128 : ℝ) ≤ (29914790831/50000000000000000000 : ℝ) := by
    have hpowers : (553/100000 : ℝ)^523 ≤ (29914790831/50000000000000000000 : ℝ)^128 := by
      have hnat : (553 : ℕ)^523*50000000000000000000^128 ≤ 29914790831^128*100000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        553 100000 29914790831 50000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (553/100000 : ℝ)) (X := (29914790831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (5537/20000 : ℝ) ^ (523/128 : ℝ) ≤ (263036492564700127/50000000000000000000 : ℝ) := by
    have hpowers : (5537/20000 : ℝ)^523 ≤ (263036492564700127/50000000000000000000 : ℝ)^128 := by
      have hnat : (5537 : ℕ)^523*50000000000000000000^128 ≤ 263036492564700127^128*20000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5537 20000 263036492564700127 50000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5537/20000 : ℝ)) (X := (263036492564700127/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000029914790831/25000000000000000000 : ℝ) ≤ (10000000002928561/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (25000000029914790831/25000000000000000000 : ℝ)^128 ≤ (10000000002928561/10000000000000000 : ℝ)^523 := by
      have hnat : (25000000029914790831 : ℕ)^128*10000000000000000^523 ≤ 10000000002928561^523*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000029914790831 25000000000000000000 10000000002928561 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000002928561/10000000000000000 : ℝ)) (X := (25000000029914790831/25000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25131518261239745479/25000000000000000000 : ℝ) ≤ (2503212427692257/2500000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (25131518261239745479/25000000000000000000 : ℝ)^128 ≤ (2503212427692257/2500000000000000 : ℝ)^523 := by
      have hnat : (25131518261239745479 : ℕ)^128*2500000000000000^523 ≤ 2503212427692257^523*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25131518261239745479 25000000000000000000 2503212427692257 2500000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503212427692257/2500000000000000 : ℝ)) (X := (25131518261239745479/25000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25263036492564700127/25000000000000000000 : ℝ) ≤ (2005139883721899/2000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (25263036492564700127/25000000000000000000 : ℝ)^128 ≤ (2005139883721899/2000000000000000 : ℝ)^523 := by
      have hnat : (25263036492564700127 : ℕ)^128*2000000000000000^523 ≤ 2005139883721899^523*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25263036492564700127 25000000000000000000 2005139883721899 2000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005139883721899/2000000000000000 : ℝ)) (X := (25263036492564700127/25000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(29914790831/50000000000000000000 : ℝ) ≤ ((775159395150246173/775200000000000000 : ℝ)+2*(12849707840467/2713200000000000 : ℝ)*(553/100000 : ℝ))^(523/128 : ℝ) := by
    rw [show (775159395150246173/775200000000000000 : ℝ)+2*(12849707840467/2713200000000000 : ℝ)*(553/100000 : ℝ)=(10000000002928561/10000000000000000 : ℝ) by norm_num, show 1+2*(29914790831/50000000000000000000 : ℝ)=(25000000029914790831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(263036492564700127/50000000000000000000 : ℝ)+(29914790831/50000000000000000000 : ℝ) ≤ ((775159395150246173/775200000000000000 : ℝ)+(12849707840467/2713200000000000 : ℝ)*((5537/20000 : ℝ)+(553/100000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (775159395150246173/775200000000000000 : ℝ)+(12849707840467/2713200000000000 : ℝ)*((5537/20000 : ℝ)+(553/100000 : ℝ))=(2503212427692257/2500000000000000 : ℝ) by norm_num, show 1+(263036492564700127/50000000000000000000 : ℝ)+(29914790831/50000000000000000000 : ℝ)=(25131518261239745479/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(263036492564700127/50000000000000000000 : ℝ) ≤ ((775159395150246173/775200000000000000 : ℝ)+2*(12849707840467/2713200000000000 : ℝ)*(5537/20000 : ℝ))^(523/128 : ℝ) := by
    rw [show (775159395150246173/775200000000000000 : ℝ)+2*(12849707840467/2713200000000000 : ℝ)*(5537/20000 : ℝ)=(2005139883721899/2000000000000000 : ℝ) by norm_num, show 1+2*(263036492564700127/50000000000000000000 : ℝ)=(25263036492564700127/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (775159395150246173/775200000000000000 : ℝ)*(X 1 0+X 2 0)+(12849707840467/2713200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (553/100000 : ℝ)) (hi := (5537/20000 : ℝ)) (c := (775159395150246173/775200000000000000 : ℝ)) (alpha := (12849707840467/2713200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (775159395150246173/775200000000000000 : ℝ)*(X 0 1+X 2 1)+(12849707840467/2713200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (553/100000 : ℝ)) (hi := (5537/20000 : ℝ)) (c := (775159395150246173/775200000000000000 : ℝ)) (alpha := (12849707840467/2713200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (775159395150246173/775200000000000000 : ℝ)*(X 0 2+X 1 2)+(12849707840467/2713200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (553/100000 : ℝ)) (hi := (5537/20000 : ℝ)) (c := (775159395150246173/775200000000000000 : ℝ)) (alpha := (12849707840467/2713200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2083300853/10000000000 : ℝ)*X 0 0+(1423127139/2500000000 : ℝ)*X 0 1+(500931357/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541725633/1000000000 : ℝ)*X 1 0+(-490271531/2000000000 : ℝ)*X 1 1+(250465631/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417258431/10000000000 : ℝ)*X 2 0+(1001862127/2000000000 : ℝ)*X 2 1+(-2451357441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157274573/5000000000 : ℝ)*X 0 0+(3683399731/10000000000 : ℝ)*X 0 1+(5051663071/10000000000 : ℝ)*X 0 2+(2157274573/5000000000 : ℝ)*X 1 0+(3683399731/10000000000 : ℝ)*X 1 1+(5051663071/10000000000 : ℝ)*X 1 2+(2157274573/5000000000 : ℝ)*X 2 0+(3683399731/10000000000 : ℝ)*X 2 1+(5051663071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208406427/1000000000 : ℝ)*X 0 0+(501852109/1000000000 : ℝ)*X 0 1+(5683118271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241801827/10000000000 : ℝ)*X 1 0+(-888774779/5000000000 : ℝ)*X 1 1+(5683120629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620900653/5000000000 : ℝ)*X 2 0+(5683121709/10000000000 : ℝ)*X 2 1+(-71101949/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158033349/5000000000 : ℝ)*X 0 0+(2516613059/5000000000 : ℝ)*X 0 1+(3702198517/10000000000 : ℝ)*X 0 2+(2158033349/5000000000 : ℝ)*X 1 0+(2516613059/5000000000 : ℝ)*X 1 1+(3702198517/10000000000 : ℝ)*X 1 2+(2158033349/5000000000 : ℝ)*X 2 0+(2516613059/5000000000 : ℝ)*X 2 1+(3702198517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (292163107007810748724024403/90440000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370882637/100000000000000 : ℝ)*(base1) + (864482873/100000000000000 : ℝ)*(base19) + (534954611/50000000000000 : ℝ)*(base23) + (79206623/25000000000000 : ℝ)*(base37) + (36505313/20000000000000 : ℝ)*(lower2) + (1097281352962073/100000000000000 : ℝ)*(major0) + (1097281352962073/100000000000000 : ℝ)*(major1) + (1097281352962073/100000000000000 : ℝ)*(major2) + (1463710534067823/100000000000000 : ℝ)*(sp0) + (178675644619/12207031250 : ℝ)*(sp1) + (365927473414569/25000000000000 : ℝ)*(sp2) + (36542508266559/5000000000000 : ℝ)*(sp3) + (197752067/12500000000000 : ℝ)*(sp4) + (48852139/6250000000000 : ℝ)*(sp6) + (730850853040309/100000000000000 : ℝ)*(f.failure) + (1463711745201721/100000000000000 : ℝ)*(f.sum) + (126302446783969/135660000000000000000000000000 : ℝ)*base66 + (192717662595838403/542640000000000000000000000000000 : ℝ)*base67 + (2396701127472481597/542640000000000000000000000000000 : ℝ)*base70 + (75762619676158403/542640000000000000000000000000000 : ℝ)*base71 + (256085736844309/135660000000000000000000000000 : ℝ)*base74 + (301174344632641597/542640000000000000000000000000000 : ℝ)*base76 + (463140576786241597/542640000000000000000000000000000 : ℝ)*base78 + (2725489693418881597/542640000000000000000000000000000 : ℝ)*base80 + (341433041090149/135660000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6333989/10000000000000000000000 : ℝ)*base89 + (6333989/10000000000000000000000 : ℝ)*base91 + (6333989/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62672717223948777371251431/11305000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (490597157/20000000000000 : ℝ)*(base19) + (299657287/10000000000000 : ℝ)*(base23) + (66863541/25000000000000 : ℝ)*(upper2) + (537467129/100000000000000 : ℝ)*(upper3) + (17059331/6250000000000 : ℝ)*(upper5) + (281995840091979/25000000000000 : ℝ)*(major0) + (281995840091979/25000000000000 : ℝ)*(major1) + (281995840091979/25000000000000 : ℝ)*(major2) + (13004558801/100000000000000 : ℝ)*(sp1) + (18468740911/100000000000000 : ℝ)*(sp2) + (752333212989931/50000000000000 : ℝ)*(sp4) + (376162742108819/25000000000000 : ℝ)*(sp5) + (1504644960666081/100000000000000 : ℝ)*(sp6) + (751300109962463/100000000000000 : ℝ)*(sp7) + (751300109962463/100000000000000 : ℝ)*(f.failure) + (752333212989931/50000000000000 : ℝ)*(f.sum) + (2013914268361/11305000000000000000000000000 : ℝ)*base65 + (196493915797876477/45220000000000000000000000000000 : ℝ)*base68 + (173607918940143523/45220000000000000000000000000000 : ℝ)*base69 + (40283948732883523/45220000000000000000000000000000 : ℝ)*base71 + (3685513176553/1413125000000000000000000000 : ℝ)*base74 + (107676316853303523/45220000000000000000000000000000 : ℝ)*base75 + (65491256881983523/45220000000000000000000000000000 : ℝ)*base77 + (20532630878643523/45220000000000000000000000000000 : ℝ)*base79 + (7624567420439/2826250000000000000000000000 : ℝ)*base81 + (2125777/10000000000000000000000 : ℝ)*base90 + (2125777/10000000000000000000000 : ℝ)*base92 + (2125777/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1176_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5537/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2919/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1176_s2_0 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-266840633/1250000000 : ℝ)*x 0 + (5504459263/10000000000 : ℝ)*x 1 + (2582315157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266840633/1250000000 : ℝ)^8369 ≤ (12943423617009/100000000000000 : ℝ)^6321 := by
    have hnat : (266840633 : ℕ)^8369*100000000000000^6321 ≤ 12943423617009^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266840633 1250000000 12943423617009 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504459263/10000000000 : ℝ)^8369 ≤ (45363481362037/100000000000000 : ℝ)^6321 := by
    have hnat : (5504459263 : ℕ)^8369*100000000000000^6321 ≤ 45363481362037^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504459263 10000000000 45363481362037 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582315157/5000000000 : ℝ)^8369 ≤ (41693095010681/100000000000000 : ℝ)^6321 := by
    have hnat : (2582315157 : ℕ)^8369*100000000000000^6321 ≤ 41693095010681^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582315157 5000000000 41693095010681 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266840633/1250000000 : ℝ), (5504459263/10000000000 : ℝ), (2582315157/5000000000 : ℝ)] ![(12943423617009/100000000000000 : ℝ), (45363481362037/100000000000000 : ℝ), (41693095010681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266840633/1250000000 : ℝ)|^8369 ≤ (12943423617009/100000000000000 : ℝ)^6321
        have hw : |(-266840633/1250000000 : ℝ)|=(266840633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504459263/10000000000 : ℝ)|^8369 ≤ (45363481362037/100000000000000 : ℝ)^6321
        have hw : |(5504459263/10000000000 : ℝ)|=(5504459263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2582315157/5000000000 : ℝ)|^8369 ≤ (41693095010681/100000000000000 : ℝ)^6321
        have hw : |(2582315157/5000000000 : ℝ)|=(2582315157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s2_1 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5372417027/10000000000 : ℝ)*x 0 + (-1155585883/5000000000 : ℝ)*x 1 + (5164633479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372417027/10000000000 : ℝ)^8369 ≤ (21964174236717/50000000000000 : ℝ)^6321 := by
    have hnat : (5372417027 : ℕ)^8369*50000000000000^6321 ≤ 21964174236717^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372417027 10000000000 21964174236717 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155585883/5000000000 : ℝ)^8369 ≤ (14378522665149/100000000000000 : ℝ)^6321 := by
    have hnat : (1155585883 : ℕ)^8369*100000000000000^6321 ≤ 14378522665149^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155585883 5000000000 14378522665149 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5164633479/10000000000 : ℝ)^8369 ≤ (41693128839469/100000000000000 : ℝ)^6321 := by
    have hnat : (5164633479 : ℕ)^8369*100000000000000^6321 ≤ 41693128839469^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164633479 10000000000 41693128839469 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372417027/10000000000 : ℝ), (-1155585883/5000000000 : ℝ), (5164633479/10000000000 : ℝ)] ![(21964174236717/50000000000000 : ℝ), (14378522665149/100000000000000 : ℝ), (41693128839469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372417027/10000000000 : ℝ)|^8369 ≤ (21964174236717/50000000000000 : ℝ)^6321
        have hw : |(5372417027/10000000000 : ℝ)|=(5372417027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1155585883/5000000000 : ℝ)|^8369 ≤ (14378522665149/100000000000000 : ℝ)^6321
        have hw : |(-1155585883/5000000000 : ℝ)|=(1155585883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5164633479/10000000000 : ℝ)|^8369 ≤ (41693128839469/100000000000000 : ℝ)^6321
        have hw : |(5164633479/10000000000 : ℝ)|=(5164633479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s2_2 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335776119/625000000 : ℝ)*x 0 + (5164632149/10000000000 : ℝ)*x 1 + (-115558617/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335776119/625000000 : ℝ)^8369 ≤ (1757134318709/4000000000000 : ℝ)^6321 := by
    have hnat : (335776119 : ℕ)^8369*4000000000000^6321 ≤ 1757134318709^6321*625000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335776119 625000000 1757134318709 4000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5164632149/10000000000 : ℝ)^8369 ≤ (8338622924779/20000000000000 : ℝ)^6321 := by
    have hnat : (5164632149 : ℕ)^8369*20000000000000^6321 ≤ 8338622924779^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164632149 10000000000 8338622924779 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115558617/500000000 : ℝ)^8369 ≤ (2875705478639/20000000000000 : ℝ)^6321 := by
    have hnat : (115558617 : ℕ)^8369*20000000000000^6321 ≤ 2875705478639^6321*500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115558617 500000000 2875705478639 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335776119/625000000 : ℝ), (5164632149/10000000000 : ℝ), (-115558617/500000000 : ℝ)] ![(1757134318709/4000000000000 : ℝ), (8338622924779/20000000000000 : ℝ), (2875705478639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335776119/625000000 : ℝ)|^8369 ≤ (1757134318709/4000000000000 : ℝ)^6321
        have hw : |(335776119/625000000 : ℝ)|=(335776119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5164632149/10000000000 : ℝ)|^8369 ≤ (8338622924779/20000000000000 : ℝ)^6321
        have hw : |(5164632149/10000000000 : ℝ)|=(5164632149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115558617/500000000 : ℝ)|^8369 ≤ (2875705478639/20000000000000 : ℝ)^6321
        have hw : |(-115558617/500000000 : ℝ)|=(115558617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s2_3 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087477257/2500000000 : ℝ)*x 0 + (50283791/125000000 : ℝ)*x 1 + (4703291257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087477257/2500000000 : ℝ)^8369 ≤ (33216049550551/100000000000000 : ℝ)^6321 := by
    have hnat : (1087477257 : ℕ)^8369*100000000000000^6321 ≤ 33216049550551^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087477257 2500000000 33216049550551 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50283791/125000000 : ℝ)^8369 ≤ (5989796633557/20000000000000 : ℝ)^6321 := by
    have hnat : (50283791 : ℕ)^8369*20000000000000^6321 ≤ 5989796633557^6321*125000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50283791 125000000 5989796633557 20000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4703291257/10000000000 : ℝ)^8369 ≤ (18417483631199/50000000000000 : ℝ)^6321 := by
    have hnat : (4703291257 : ℕ)^8369*50000000000000^6321 ≤ 18417483631199^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4703291257 10000000000 18417483631199 50000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087477257/2500000000 : ℝ), (50283791/125000000 : ℝ), (4703291257/10000000000 : ℝ)] ![(33216049550551/100000000000000 : ℝ), (5989796633557/20000000000000 : ℝ), (18417483631199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087477257/2500000000 : ℝ)|^8369 ≤ (33216049550551/100000000000000 : ℝ)^6321
        have hw : |(1087477257/2500000000 : ℝ)|=(1087477257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50283791/125000000 : ℝ)|^8369 ≤ (5989796633557/20000000000000 : ℝ)^6321
        have hw : |(50283791/125000000 : ℝ)|=(50283791/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4703291257/10000000000 : ℝ)|^8369 ≤ (18417483631199/50000000000000 : ℝ)^6321
        have hw : |(4703291257/10000000000 : ℝ)|=(4703291257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s2_4 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-426963579/2000000000 : ℝ)*x 0 + (5166919259/10000000000 : ℝ)*x 1 + (1375537119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426963579/2000000000 : ℝ)^8369 ≤ (129441688483/1000000000000 : ℝ)^6321 := by
    have hnat : (426963579 : ℕ)^8369*1000000000000^6321 ≤ 129441688483^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426963579 2000000000 129441688483 1000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5166919259/10000000000 : ℝ)^8369 ≤ (834351238507/2000000000000 : ℝ)^6321 := by
    have hnat : (5166919259 : ℕ)^8369*2000000000000^6321 ≤ 834351238507^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166919259 10000000000 834351238507 2000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375537119/2500000000 : ℝ)^8369 ≤ (45338269212841/100000000000000 : ℝ)^6321 := by
    have hnat : (1375537119 : ℕ)^8369*100000000000000^6321 ≤ 45338269212841^6321*2500000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375537119 2500000000 45338269212841 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426963579/2000000000 : ℝ), (5166919259/10000000000 : ℝ), (1375537119/2500000000 : ℝ)] ![(129441688483/1000000000000 : ℝ), (834351238507/2000000000000 : ℝ), (45338269212841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426963579/2000000000 : ℝ)|^8369 ≤ (129441688483/1000000000000 : ℝ)^6321
        have hw : |(-426963579/2000000000 : ℝ)|=(426963579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5166919259/10000000000 : ℝ)|^8369 ≤ (834351238507/2000000000000 : ℝ)^6321
        have hw : |(5166919259/10000000000 : ℝ)|=(5166919259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1375537119/2500000000 : ℝ)|^8369 ≤ (45338269212841/100000000000000 : ℝ)^6321
        have hw : |(1375537119/2500000000 : ℝ)|=(1375537119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s2_5 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057199983/2000000000 : ℝ)*x 0 + (-1973655459/10000000000 : ℝ)*x 1 + (2751074239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057199983/2000000000 : ℝ)^8369 ≤ (5374406815147/12500000000000 : ℝ)^6321 := by
    have hnat : (1057199983 : ℕ)^8369*12500000000000^6321 ≤ 5374406815147^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057199983 2000000000 5374406815147 12500000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973655459/10000000000 : ℝ)^8369 ≤ (11666476225257/100000000000000 : ℝ)^6321 := by
    have hnat : (1973655459 : ℕ)^8369*100000000000000^6321 ≤ 11666476225257^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973655459 10000000000 11666476225257 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751074239/5000000000 : ℝ)^8369 ≤ (45338269234661/100000000000000 : ℝ)^6321 := by
    have hnat : (2751074239 : ℕ)^8369*100000000000000^6321 ≤ 45338269234661^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751074239 5000000000 45338269234661 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057199983/2000000000 : ℝ), (-1973655459/10000000000 : ℝ), (2751074239/5000000000 : ℝ)] ![(5374406815147/12500000000000 : ℝ), (11666476225257/100000000000000 : ℝ), (45338269234661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057199983/2000000000 : ℝ)|^8369 ≤ (5374406815147/12500000000000 : ℝ)^6321
        have hw : |(1057199983/2000000000 : ℝ)|=(1057199983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1973655459/10000000000 : ℝ)|^8369 ≤ (11666476225257/100000000000000 : ℝ)^6321
        have hw : |(-1973655459/10000000000 : ℝ)|=(1973655459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751074239/5000000000 : ℝ)|^8369 ≤ (45338269234661/100000000000000 : ℝ)^6321
        have hw : |(2751074239/5000000000 : ℝ)|=(2751074239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s2_6 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660750007/1250000000 : ℝ)*x 0 + (2751074239/5000000000 : ℝ)*x 1 + (-394731053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660750007/1250000000 : ℝ)^8369 ≤ (343962048317/800000000000 : ℝ)^6321 := by
    have hnat : (660750007 : ℕ)^8369*800000000000^6321 ≤ 343962048317^6321*1250000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660750007 1250000000 343962048317 800000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751074239/5000000000 : ℝ)^8369 ≤ (45338269234661/100000000000000 : ℝ)^6321 := by
    have hnat : (2751074239 : ℕ)^8369*100000000000000^6321 ≤ 45338269234661^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751074239 5000000000 45338269234661 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394731053/2000000000 : ℝ)^8369 ≤ (2916618676739/25000000000000 : ℝ)^6321 := by
    have hnat : (394731053 : ℕ)^8369*25000000000000^6321 ≤ 2916618676739^6321*2000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394731053 2000000000 2916618676739 25000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660750007/1250000000 : ℝ), (2751074239/5000000000 : ℝ), (-394731053/2000000000 : ℝ)] ![(343962048317/800000000000 : ℝ), (45338269234661/100000000000000 : ℝ), (2916618676739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660750007/1250000000 : ℝ)|^8369 ≤ (343962048317/800000000000 : ℝ)^6321
        have hw : |(660750007/1250000000 : ℝ)|=(660750007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751074239/5000000000 : ℝ)|^8369 ≤ (45338269234661/100000000000000 : ℝ)^6321
        have hw : |(2751074239/5000000000 : ℝ)|=(2751074239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394731053/2000000000 : ℝ)|^8369 ≤ (2916618676739/25000000000000 : ℝ)^6321
        have hw : |(-394731053/2000000000 : ℝ)|=(394731053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1176_s2_7 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350096727/10000000000 : ℝ)*x 0 + (4698709619/10000000000 : ℝ)*x 1 + (2013664393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350096727/10000000000 : ℝ)^8369 ≤ (33217947220051/100000000000000 : ℝ)^6321 := by
    have hnat : (4350096727 : ℕ)^8369*100000000000000^6321 ≤ 33217947220051^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350096727 10000000000 33217947220051 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4698709619/10000000000 : ℝ)^8369 ≤ (22992166711/62500000000 : ℝ)^6321 := by
    have hnat : (4698709619 : ℕ)^8369*62500000000^6321 ≤ 22992166711^6321*10000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698709619 10000000000 22992166711 62500000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013664393/5000000000 : ℝ)^8369 ≤ (29994586017047/100000000000000 : ℝ)^6321 := by
    have hnat : (2013664393 : ℕ)^8369*100000000000000^6321 ≤ 29994586017047^6321*5000000000^8369 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013664393 5000000000 29994586017047 100000000000000 8369 6321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8369/2048 : ℝ)) 8369 6321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350096727/10000000000 : ℝ), (4698709619/10000000000 : ℝ), (2013664393/5000000000 : ℝ)] ![(33217947220051/100000000000000 : ℝ), (22992166711/62500000000 : ℝ), (29994586017047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350096727/10000000000 : ℝ)|^8369 ≤ (33217947220051/100000000000000 : ℝ)^6321
        have hw : |(4350096727/10000000000 : ℝ)|=(4350096727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4698709619/10000000000 : ℝ)|^8369 ≤ (22992166711/62500000000 : ℝ)^6321
        have hw : |(4698709619/10000000000 : ℝ)|=(4698709619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013664393/5000000000 : ℝ)|^8369 ≤ (29994586017047/100000000000000 : ℝ)^6321
        have hw : |(2013664393/5000000000 : ℝ)|=(2013664393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1176_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2919/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9221/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16403/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4057/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2919/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4057/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2919/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4057/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2919/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4057/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2919/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4057/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2919/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4057/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2919/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2919/50000 : ℝ) ^ (523/128 : ℝ) ≤ (113747587902289/12500000000000000000 : ℝ) := by
    have hpowers : (2919/50000 : ℝ)^523 ≤ (113747587902289/12500000000000000000 : ℝ)^128 := by
      have hnat : (2919 : ℕ)^523*12500000000000000000^128 ≤ 113747587902289^128*50000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2919 50000 113747587902289 12500000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2919/50000 : ℝ)) (X := (113747587902289/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hpowhi : (4057/20000 : ℝ) ^ (523/128 : ℝ) ≤ (147625166607042671/100000000000000000000 : ℝ) := by
    have hpowers : (4057/20000 : ℝ)^523 ≤ (147625166607042671/100000000000000000000 : ℝ)^128 := by
      have hnat : (4057 : ℕ)^523*100000000000000000000^128 ≤ 147625166607042671^128*20000^523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4057 20000 147625166607042671 100000000000000000000 523 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4057/20000 : ℝ)) (X := (147625166607042671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250113747587902289/6250000000000000000 : ℝ) ≤ (5000022270885183/5000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (6250113747587902289/6250000000000000000 : ℝ)^128 ≤ (5000022270885183/5000000000000000 : ℝ)^523 := by
      have hnat : (6250113747587902289 : ℕ)^128*5000000000000000^523 ≤ 5000022270885183^523*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250113747587902289 6250000000000000000 5000022270885183 5000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000022270885183/5000000000000000 : ℝ)) (X := (6250113747587902289/6250000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100148535147310260983/100000000000000000000 : ℝ) ≤ (10003633239728031/10000000000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (100148535147310260983/100000000000000000000 : ℝ)^128 ≤ (10003633239728031/10000000000000000 : ℝ)^523 := by
      have hnat : (100148535147310260983 : ℕ)^128*10000000000000000^523 ≤ 10003633239728031^523*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100148535147310260983 100000000000000000000 10003633239728031 10000000000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003633239728031/10000000000000000 : ℝ)) (X := (100148535147310260983/100000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50147625166607042671/50000000000000000000 : ℝ) ≤ (156362842776339/156250000000000 : ℝ) ^ (523/128 : ℝ) := by
    have hpowers : (50147625166607042671/50000000000000000000 : ℝ)^128 ≤ (156362842776339/156250000000000 : ℝ)^523 := by
      have hnat : (50147625166607042671 : ℕ)^128*156250000000000^523 ≤ 156362842776339^523*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50147625166607042671 50000000000000000000 156362842776339 156250000000000 128 523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156362842776339/156250000000000 : ℝ)) (X := (50147625166607042671/50000000000000000000 : ℝ)) (by norm_num) 523 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(113747587902289/12500000000000000000 : ℝ) ≤ ((72214370928801390531/72235000000000000000 : ℝ)+2*(717739591533/288940000000000 : ℝ)*(2919/50000 : ℝ))^(523/128 : ℝ) := by
    rw [show (72214370928801390531/72235000000000000000 : ℝ)+2*(717739591533/288940000000000 : ℝ)*(2919/50000 : ℝ)=(5000022270885183/5000000000000000 : ℝ) by norm_num, show 1+2*(113747587902289/12500000000000000000 : ℝ)=(6250113747587902289/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(147625166607042671/100000000000000000000 : ℝ)+(113747587902289/12500000000000000000 : ℝ) ≤ ((72214370928801390531/72235000000000000000 : ℝ)+(717739591533/288940000000000 : ℝ)*((4057/20000 : ℝ)+(2919/50000 : ℝ)))^(523/128 : ℝ) := by
    rw [show (72214370928801390531/72235000000000000000 : ℝ)+(717739591533/288940000000000 : ℝ)*((4057/20000 : ℝ)+(2919/50000 : ℝ))=(10003633239728031/10000000000000000 : ℝ) by norm_num, show 1+(147625166607042671/100000000000000000000 : ℝ)+(113747587902289/12500000000000000000 : ℝ)=(100148535147310260983/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(147625166607042671/100000000000000000000 : ℝ) ≤ ((72214370928801390531/72235000000000000000 : ℝ)+2*(717739591533/288940000000000 : ℝ)*(4057/20000 : ℝ))^(523/128 : ℝ) := by
    rw [show (72214370928801390531/72235000000000000000 : ℝ)+2*(717739591533/288940000000000 : ℝ)*(4057/20000 : ℝ)=(156362842776339/156250000000000 : ℝ) by norm_num, show 1+2*(147625166607042671/100000000000000000000 : ℝ)=(50147625166607042671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72214370928801390531/72235000000000000000 : ℝ)*(X 1 0+X 2 0)+(717739591533/288940000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2919/50000 : ℝ)) (hi := (4057/20000 : ℝ)) (c := (72214370928801390531/72235000000000000000 : ℝ)) (alpha := (717739591533/288940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72214370928801390531/72235000000000000000 : ℝ)*(X 0 1+X 2 1)+(717739591533/288940000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2919/50000 : ℝ)) (hi := (4057/20000 : ℝ)) (c := (72214370928801390531/72235000000000000000 : ℝ)) (alpha := (717739591533/288940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72214370928801390531/72235000000000000000 : ℝ)*(X 0 2+X 1 2)+(717739591533/288940000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (523/128 : ℝ)) (lo := (2919/50000 : ℝ)) (hi := (4057/20000 : ℝ)) (c := (72214370928801390531/72235000000000000000 : ℝ)) (alpha := (717739591533/288940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-266840633/1250000000 : ℝ)*X 0 0+(5504459263/10000000000 : ℝ)*X 0 1+(2582315157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372417027/10000000000 : ℝ)*X 1 0+(-1155585883/5000000000 : ℝ)*X 1 1+(5164633479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335776119/625000000 : ℝ)*X 2 0+(5164632149/10000000000 : ℝ)*X 2 1+(-115558617/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087477257/2500000000 : ℝ)*X 0 0+(50283791/125000000 : ℝ)*X 0 1+(4703291257/10000000000 : ℝ)*X 0 2+(1087477257/2500000000 : ℝ)*X 1 0+(50283791/125000000 : ℝ)*X 1 1+(4703291257/10000000000 : ℝ)*X 1 2+(1087477257/2500000000 : ℝ)*X 2 0+(50283791/125000000 : ℝ)*X 2 1+(4703291257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-426963579/2000000000 : ℝ)*X 0 0+(5166919259/10000000000 : ℝ)*X 0 1+(1375537119/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057199983/2000000000 : ℝ)*X 1 0+(-1973655459/10000000000 : ℝ)*X 1 1+(2751074239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660750007/1250000000 : ℝ)*X 2 0+(2751074239/5000000000 : ℝ)*X 2 1+(-394731053/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350096727/10000000000 : ℝ)*X 0 0+(4698709619/10000000000 : ℝ)*X 0 1+(2013664393/5000000000 : ℝ)*X 0 2+(4350096727/10000000000 : ℝ)*X 1 0+(4698709619/10000000000 : ℝ)*X 1 1+(2013664393/5000000000 : ℝ)*X 1 2+(4350096727/10000000000 : ℝ)*X 2 0+(4698709619/10000000000 : ℝ)*X 2 1+(2013664393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1176_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4211521015120906922088700029/451468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1236408591/100000000000000 : ℝ)*(base19) + (1365687283/100000000000000 : ℝ)*(base23) + (28519747/100000000000000 : ℝ)*(upper2) + (53897293/10000000000000 : ℝ)*(upper3) + (108571193/50000000000000 : ℝ)*(upper4) + (275753865844751/12500000000000 : ℝ)*(major0) + (275753865844751/12500000000000 : ℝ)*(major1) + (275753865844751/12500000000000 : ℝ)*(major2) + (735673004964143/25000000000000 : ℝ)*(sp0) + (1471360061264209/50000000000000 : ℝ)*(sp1) + (1471359996624863/50000000000000 : ℝ)*(sp2) + (73466296794679/5000000000000 : ℝ)*(sp3) + (29339080437/100000000000000 : ℝ)*(sp4) + (7123867903/50000000000000 : ℝ)*(sp7) + (734670091814693/50000000000000 : ℝ)*(f.failure) + (183920084933563/6250000000000 : ℝ)*(f.sum) + (109081648144151/14447000000000000000000000000 : ℝ)*base65 + (10450373952977484719/902937500000000000000000000000000 : ℝ)*base68 + (2503446083075047219/902937500000000000000000000000000 : ℝ)*base70 + (1960501901545297219/902937500000000000000000000000000 : ℝ)*base72 + (23041974733971/7223500000000000000000000000 : ℝ)*base73 + (6446952117018422219/902937500000000000000000000000000 : ℝ)*base76 + (110311648235672219/902937500000000000000000000000000 : ℝ)*base78 + (448335314482797219/902937500000000000000000000000000 : ℝ)*base80 + (12489637912409/1805875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1603947/5000000000000000000000 : ℝ)*base90 + (1603947/5000000000000000000000 : ℝ)*base92 + (1603947/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3763149987483367589133/1444700000000000000000000000 : ℝ) := by norm_num
    linear_combination (758401843/100000000000000 : ℝ)*(base19) + (950196111/100000000000000 : ℝ)*(base23) + (32400053/100000000000000 : ℝ)*(upper2) + (25768811/25000000000000 : ℝ)*(upper3) + (29665019/50000000000000 : ℝ)*(upper5) + (2236250502766731/100000000000000 : ℝ)*(major0) + (2236250502766731/100000000000000 : ℝ)*(major1) + (2236250502766731/100000000000000 : ℝ)*(major2) + (353523919/5000000000000 : ℝ)*(sp1) + (2037141197/20000000000000 : ℝ)*(sp2) + (1491516402246321/50000000000000 : ℝ)*(sp4) + (149151248780621/5000000000000 : ℝ)*(sp5) + (1491510834295273/50000000000000 : ℝ)*(sp6) + (297893622842851/20000000000000 : ℝ)*(sp7) + (297893622842851/20000000000000 : ℝ)*(f.failure) + (1491516402246321/50000000000000 : ℝ)*(f.sum) + (11114096172629/7223500000000000000000000000 : ℝ)*base65 + (12785198059309525839/7223500000000000000000000000000000 : ℝ)*base68 + (25650706665763974161/7223500000000000000000000000000000 : ℝ)*base69 + (19806852380973474161/7223500000000000000000000000000000 : ℝ)*base71 + (6914006344041/1805875000000000000000000000 : ℝ)*base73 + (58005132166754025839/7223500000000000000000000000000000 : ℝ)*base76 + (10050031519557474161/7223500000000000000000000000000000 : ℝ)*base77 + (11327556978472025839/7223500000000000000000000000000000 : ℝ)*base80 + (44308264145143/14447000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1712371/2000000000000000000000 : ℝ)*base89 + (1712371/2000000000000000000000 : ℝ)*base91 + (1712371/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1176_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2919/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16403/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1176_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1176_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16403/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1176_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1176_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1176_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150137521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16403/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1176_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
