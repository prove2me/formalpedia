-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1731_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:06:51.755331+00:00
-- url     : https://prove2.me/submissions/fbe1452a-5b97-4f19-b198-c76951548b8f

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
theorem support_rectangle_w1731_s0_0 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-319247151/2500000000 : ℝ)*x 0 + (565777339/1000000000 : ℝ)*x 1 + (996232893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319247151/2500000000 : ℝ)^5471 ≤ (7950068225019/100000000000000 : ℝ)^4447 := by
    have hnat : (319247151 : ℕ)^5471*100000000000000^4447 ≤ 7950068225019^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319247151 2500000000 7950068225019 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565777339/1000000000 : ℝ)^5471 ≤ (49623550454193/100000000000000 : ℝ)^4447 := by
    have hnat : (565777339 : ℕ)^5471*100000000000000^4447 ≤ 49623550454193^4447*1000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565777339 1000000000 49623550454193 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996232893/2000000000 : ℝ)^5471 ≤ (2651648831491/6250000000000 : ℝ)^4447 := by
    have hnat : (996232893 : ℕ)^5471*6250000000000^4447 ≤ 2651648831491^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996232893 2000000000 2651648831491 6250000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-319247151/2500000000 : ℝ), (565777339/1000000000 : ℝ), (996232893/2000000000 : ℝ)] ![(7950068225019/100000000000000 : ℝ), (49623550454193/100000000000000 : ℝ), (2651648831491/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-319247151/2500000000 : ℝ)|^5471 ≤ (7950068225019/100000000000000 : ℝ)^4447
        have hw : |(-319247151/2500000000 : ℝ)|=(319247151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565777339/1000000000 : ℝ)|^5471 ≤ (49623550454193/100000000000000 : ℝ)^4447
        have hw : |(565777339/1000000000 : ℝ)|=(565777339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(996232893/2000000000 : ℝ)|^5471 ≤ (2651648831491/6250000000000 : ℝ)^4447
        have hw : |(996232893/2000000000 : ℝ)|=(996232893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s0_1 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389995397/10000000000 : ℝ)*x 0 + (-820497007/5000000000 : ℝ)*x 1 + (4981163717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389995397/10000000000 : ℝ)^5471 ≤ (1870001222331/4000000000000 : ℝ)^4447 := by
    have hnat : (5389995397 : ℕ)^5471*4000000000000^4447 ≤ 1870001222331^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389995397 10000000000 1870001222331 4000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (820497007/5000000000 : ℝ)^5471 ≤ (10823595957751/100000000000000 : ℝ)^4447 := by
    have hnat : (820497007 : ℕ)^5471*100000000000000^4447 ≤ 10823595957751^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820497007 5000000000 10823595957751 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981163717/10000000000 : ℝ)^5471 ≤ (42426373465837/100000000000000 : ℝ)^4447 := by
    have hnat : (4981163717 : ℕ)^5471*100000000000000^4447 ≤ 42426373465837^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981163717 10000000000 42426373465837 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389995397/10000000000 : ℝ), (-820497007/5000000000 : ℝ), (4981163717/10000000000 : ℝ)] ![(1870001222331/4000000000000 : ℝ), (10823595957751/100000000000000 : ℝ), (42426373465837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389995397/10000000000 : ℝ)|^5471 ≤ (1870001222331/4000000000000 : ℝ)^4447
        have hw : |(5389995397/10000000000 : ℝ)|=(5389995397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-820497007/5000000000 : ℝ)|^5471 ≤ (10823595957751/100000000000000 : ℝ)^4447
        have hw : |(-820497007/5000000000 : ℝ)|=(820497007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4981163717/10000000000 : ℝ)|^5471 ≤ (42426373465837/100000000000000 : ℝ)^4447
        have hw : |(4981163717/10000000000 : ℝ)|=(4981163717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s0_2 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694996873/5000000000 : ℝ)*x 0 + (1245291199/2500000000 : ℝ)*x 1 + (-205124349/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694996873/5000000000 : ℝ)^5471 ≤ (23375006470471/50000000000000 : ℝ)^4447 := by
    have hnat : (2694996873 : ℕ)^5471*50000000000000^4447 ≤ 23375006470471^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694996873 5000000000 23375006470471 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1245291199/2500000000 : ℝ)^5471 ≤ (10606596193071/25000000000000 : ℝ)^4447 := by
    have hnat : (1245291199 : ℕ)^5471*25000000000000^4447 ≤ 10606596193071^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245291199 2500000000 10606596193071 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205124349/1250000000 : ℝ)^5471 ≤ (10823602270867/100000000000000 : ℝ)^4447 := by
    have hnat : (205124349 : ℕ)^5471*100000000000000^4447 ≤ 10823602270867^4447*1250000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205124349 1250000000 10823602270867 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694996873/5000000000 : ℝ), (1245291199/2500000000 : ℝ), (-205124349/1250000000 : ℝ)] ![(23375006470471/50000000000000 : ℝ), (10606596193071/25000000000000 : ℝ), (10823602270867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694996873/5000000000 : ℝ)|^5471 ≤ (23375006470471/50000000000000 : ℝ)^4447
        have hw : |(2694996873/5000000000 : ℝ)|=(2694996873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1245291199/2500000000 : ℝ)|^5471 ≤ (10606596193071/25000000000000 : ℝ)^4447
        have hw : |(1245291199/2500000000 : ℝ)|=(1245291199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-205124349/1250000000 : ℝ)|^5471 ≤ (10823602270867/100000000000000 : ℝ)^4447
        have hw : |(-205124349/1250000000 : ℝ)|=(205124349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s0_3 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (804454233/2000000000 : ℝ)*x 0 + (192026511/625000000 : ℝ)*x 1 + (5128298687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804454233/2000000000 : ℝ)^5471 ≤ (16306618750081/50000000000000 : ℝ)^4447 := by
    have hnat : (804454233 : ℕ)^5471*50000000000000^4447 ≤ 16306618750081^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804454233 2000000000 16306618750081 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192026511/625000000 : ℝ)^5471 ≤ (23413411371249/100000000000000 : ℝ)^4447 := by
    have hnat : (192026511 : ℕ)^5471*100000000000000^4447 ≤ 23413411371249^4447*625000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192026511 625000000 23413411371249 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128298687/10000000000 : ℝ)^5471 ≤ (43973351113249/100000000000000 : ℝ)^4447 := by
    have hnat : (5128298687 : ℕ)^5471*100000000000000^4447 ≤ 43973351113249^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128298687 10000000000 43973351113249 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(804454233/2000000000 : ℝ), (192026511/625000000 : ℝ), (5128298687/10000000000 : ℝ)] ![(16306618750081/50000000000000 : ℝ), (23413411371249/100000000000000 : ℝ), (43973351113249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(804454233/2000000000 : ℝ)|^5471 ≤ (16306618750081/50000000000000 : ℝ)^4447
        have hw : |(804454233/2000000000 : ℝ)|=(804454233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192026511/625000000 : ℝ)|^5471 ≤ (23413411371249/100000000000000 : ℝ)^4447
        have hw : |(192026511/625000000 : ℝ)|=(192026511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128298687/10000000000 : ℝ)|^5471 ≤ (43973351113249/100000000000000 : ℝ)^4447
        have hw : |(5128298687/10000000000 : ℝ)|=(5128298687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s0_4 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1278363957/10000000000 : ℝ)*x 0 + (312337861/625000000 : ℝ)*x 1 + (5641013499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1278363957/10000000000 : ℝ)^5471 ≤ (1592120726967/20000000000000 : ℝ)^4447 := by
    have hnat : (1278363957 : ℕ)^5471*20000000000000^4447 ≤ 1592120726967^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278363957 10000000000 1592120726967 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312337861/625000000 : ℝ)^5471 ≤ (42596631901247/100000000000000 : ℝ)^4447 := by
    have hnat : (312337861 : ℕ)^5471*100000000000000^4447 ≤ 42596631901247^4447*625000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312337861 625000000 42596631901247 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5641013499/10000000000 : ℝ)^5471 ≤ (49442764451403/100000000000000 : ℝ)^4447 := by
    have hnat : (5641013499 : ℕ)^5471*100000000000000^4447 ≤ 49442764451403^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5641013499 10000000000 49442764451403 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1278363957/10000000000 : ℝ), (312337861/625000000 : ℝ), (5641013499/10000000000 : ℝ)] ![(1592120726967/20000000000000 : ℝ), (42596631901247/100000000000000 : ℝ), (49442764451403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1278363957/10000000000 : ℝ)|^5471 ≤ (1592120726967/20000000000000 : ℝ)^4447
        have hw : |(-1278363957/10000000000 : ℝ)|=(1278363957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312337861/625000000 : ℝ)|^5471 ≤ (42596631901247/100000000000000 : ℝ)^4447
        have hw : |(312337861/625000000 : ℝ)|=(312337861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5641013499/10000000000 : ℝ)|^5471 ≤ (49442764451403/100000000000000 : ℝ)^4447
        have hw : |(5641013499/10000000000 : ℝ)|=(5641013499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s0_5 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5207339679/10000000000 : ℝ)*x 0 + (-981144547/10000000000 : ℝ)*x 1 + (352563359/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5207339679/10000000000 : ℝ)^5471 ≤ (44808637071363/100000000000000 : ℝ)^4447 := by
    have hnat : (5207339679 : ℕ)^5471*100000000000000^4447 ≤ 44808637071363^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207339679 10000000000 44808637071363 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981144547/10000000000 : ℝ)^5471 ≤ (5748595821241/100000000000000 : ℝ)^4447 := by
    have hnat : (981144547 : ℕ)^5471*100000000000000^4447 ≤ 5748595821241^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981144547 10000000000 5748595821241 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352563359/625000000 : ℝ)^5471 ≤ (6180345886659/12500000000000 : ℝ)^4447 := by
    have hnat : (352563359 : ℕ)^5471*12500000000000^4447 ≤ 6180345886659^4447*625000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352563359 625000000 6180345886659 12500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5207339679/10000000000 : ℝ), (-981144547/10000000000 : ℝ), (352563359/625000000 : ℝ)] ![(44808637071363/100000000000000 : ℝ), (5748595821241/100000000000000 : ℝ), (6180345886659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5207339679/10000000000 : ℝ)|^5471 ≤ (44808637071363/100000000000000 : ℝ)^4447
        have hw : |(5207339679/10000000000 : ℝ)|=(5207339679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-981144547/10000000000 : ℝ)|^5471 ≤ (5748595821241/100000000000000 : ℝ)^4447
        have hw : |(-981144547/10000000000 : ℝ)|=(981144547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352563359/625000000 : ℝ)|^5471 ≤ (6180345886659/12500000000000 : ℝ)^4447
        have hw : |(352563359/625000000 : ℝ)|=(352563359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s0_6 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5207339223/10000000000 : ℝ)*x 0 + (1410253393/2500000000 : ℝ)*x 1 + (-490572737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5207339223/10000000000 : ℝ)^5471 ≤ (44808632243997/100000000000000 : ℝ)^4447 := by
    have hnat : (5207339223 : ℕ)^5471*100000000000000^4447 ≤ 44808632243997^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207339223 10000000000 44808632243997 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1410253393/2500000000 : ℝ)^5471 ≤ (12360691309643/25000000000000 : ℝ)^4447 := by
    have hnat : (1410253393 : ℕ)^5471*25000000000000^4447 ≤ 12360691309643^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1410253393 2500000000 12360691309643 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490572737/5000000000 : ℝ)^5471 ≤ (5748602503267/100000000000000 : ℝ)^4447 := by
    have hnat : (490572737 : ℕ)^5471*100000000000000^4447 ≤ 5748602503267^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490572737 5000000000 5748602503267 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5207339223/10000000000 : ℝ), (1410253393/2500000000 : ℝ), (-490572737/5000000000 : ℝ)] ![(44808632243997/100000000000000 : ℝ), (12360691309643/25000000000000 : ℝ), (5748602503267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5207339223/10000000000 : ℝ)|^5471 ≤ (44808632243997/100000000000000 : ℝ)^4447
        have hw : |(5207339223/10000000000 : ℝ)|=(5207339223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1410253393/2500000000 : ℝ)|^5471 ≤ (12360691309643/25000000000000 : ℝ)^4447
        have hw : |(1410253393/2500000000 : ℝ)|=(1410253393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490572737/5000000000 : ℝ)|^5471 ≤ (5748602503267/100000000000000 : ℝ)^4447
        have hw : |(-490572737/5000000000 : ℝ)|=(490572737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s0_7 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (161057881/400000000 : ℝ)*x 0 + (2539476019/5000000000 : ℝ)*x 1 + (3123347359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161057881/400000000 : ℝ)^5471 ≤ (2040931098027/6250000000000 : ℝ)^4447 := by
    have hnat : (161057881 : ℕ)^5471*6250000000000^4447 ≤ 2040931098027^4447*400000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161057881 400000000 2040931098027 6250000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539476019/5000000000 : ℝ)^5471 ≤ (8690673201943/20000000000000 : ℝ)^4447 := by
    have hnat : (2539476019 : ℕ)^5471*20000000000000^4447 ≤ 8690673201943^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539476019 5000000000 8690673201943 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3123347359/10000000000 : ℝ)^5471 ≤ (2389173640783/10000000000000 : ℝ)^4447 := by
    have hnat : (3123347359 : ℕ)^5471*10000000000000^4447 ≤ 2389173640783^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123347359 10000000000 2389173640783 10000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161057881/400000000 : ℝ), (2539476019/5000000000 : ℝ), (3123347359/10000000000 : ℝ)] ![(2040931098027/6250000000000 : ℝ), (8690673201943/20000000000000 : ℝ), (2389173640783/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161057881/400000000 : ℝ)|^5471 ≤ (2040931098027/6250000000000 : ℝ)^4447
        have hw : |(161057881/400000000 : ℝ)|=(161057881/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539476019/5000000000 : ℝ)|^5471 ≤ (8690673201943/20000000000000 : ℝ)^4447
        have hw : |(2539476019/5000000000 : ℝ)|=(2539476019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3123347359/10000000000 : ℝ)|^5471 ≤ (2389173640783/10000000000000 : ℝ)^4447
        have hw : |(3123347359/10000000000 : ℝ)|=(3123347359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1731_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (207/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10601/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5463/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5463 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5463*1^1024 ≤ 0^1024*1^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5463/1024 : ℝ) ≤ (376682637457245989/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5463 ≤ (376682637457245989/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5463*50000000000000000000^1024 ≤ 376682637457245989^1024*5^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 376682637457245989 50000000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (376682637457245989/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5463 := by
      have hnat : (1 : ℕ)^1024*1^5463 ≤ 1^5463*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50376682637457245989/50000000000000000000 : ℝ) ≤ (10014078263222461/10000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (50376682637457245989/50000000000000000000 : ℝ)^1024 ≤ (10014078263222461/10000000000000000 : ℝ)^5463 := by
      have hnat : (50376682637457245989 : ℕ)^1024*10000000000000000^5463 ≤ 10014078263222461^5463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50376682637457245989 50000000000000000000 10014078263222461 10000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014078263222461/10000000000000000 : ℝ)) (X := (50376682637457245989/50000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25376682637457245989/25000000000000000000 : ℝ) ≤ (5014078263222461/5000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (25376682637457245989/25000000000000000000 : ℝ)^1024 ≤ (5014078263222461/5000000000000000 : ℝ)^5463 := by
      have hnat : (25376682637457245989 : ℕ)^1024*5000000000000000^5463 ≤ 5014078263222461^5463*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25376682637457245989 25000000000000000000 5014078263222461 5000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014078263222461/5000000000000000 : ℝ)) (X := (25376682637457245989/25000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14078263222461/4000000000000000 : ℝ)*(0 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14078263222461/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(376682637457245989/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14078263222461/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5463/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14078263222461/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10014078263222461/10000000000000000 : ℝ) by norm_num, show 1+(376682637457245989/50000000000000000000 : ℝ)+(0 : ℝ)=(50376682637457245989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(376682637457245989/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14078263222461/4000000000000000 : ℝ)*(2/5 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14078263222461/4000000000000000 : ℝ)*(2/5 : ℝ)=(5014078263222461/5000000000000000 : ℝ) by norm_num, show 1+2*(376682637457245989/50000000000000000000 : ℝ)=(25376682637457245989/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14078263222461/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14078263222461/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14078263222461/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14078263222461/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14078263222461/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14078263222461/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-319247151/2500000000 : ℝ)*X 0 0+(565777339/1000000000 : ℝ)*X 0 1+(996232893/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5389995397/10000000000 : ℝ)*X 1 0+(-820497007/5000000000 : ℝ)*X 1 1+(4981163717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2694996873/5000000000 : ℝ)*X 2 0+(1245291199/2500000000 : ℝ)*X 2 1+(-205124349/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((804454233/2000000000 : ℝ)*X 0 0+(192026511/625000000 : ℝ)*X 0 1+(5128298687/10000000000 : ℝ)*X 0 2+(804454233/2000000000 : ℝ)*X 1 0+(192026511/625000000 : ℝ)*X 1 1+(5128298687/10000000000 : ℝ)*X 1 2+(804454233/2000000000 : ℝ)*X 2 0+(192026511/625000000 : ℝ)*X 2 1+(5128298687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1278363957/10000000000 : ℝ)*X 0 0+(312337861/625000000 : ℝ)*X 0 1+(5641013499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5207339679/10000000000 : ℝ)*X 1 0+(-981144547/10000000000 : ℝ)*X 1 1+(352563359/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5207339223/10000000000 : ℝ)*X 2 0+(1410253393/2500000000 : ℝ)*X 2 1+(-490572737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((161057881/400000000 : ℝ)*X 0 0+(2539476019/5000000000 : ℝ)*X 0 1+(3123347359/10000000000 : ℝ)*X 0 2+(161057881/400000000 : ℝ)*X 1 0+(2539476019/5000000000 : ℝ)*X 1 1+(3123347359/10000000000 : ℝ)*X 1 2+(161057881/400000000 : ℝ)*X 2 0+(2539476019/5000000000 : ℝ)*X 2 1+(3123347359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (745155354461656815569841/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253865493/100000000000000 : ℝ)*(base1) + (1677472873/100000000000000 : ℝ)*(base19) + (12247593/1000000000000 : ℝ)*(base23) + (88121001/20000000000000 : ℝ)*(upper3) + (6125219/50000000000000 : ℝ)*(upper5) + (982191292626473/100000000000000 : ℝ)*(major0) + (982191292626473/100000000000000 : ℝ)*(major1) + (982191292626473/100000000000000 : ℝ)*(major2) + (738983164156507/50000000000000 : ℝ)*(sp0) + (738983443351927/50000000000000 : ℝ)*(sp1) + (1477967339417427/100000000000000 : ℝ)*(sp2) + (243205818868697/50000000000000 : ℝ)*(sp3) + (1244864603/50000000000000 : ℝ)*(sp4) + (1881088203/100000000000000 : ℝ)*(sp7) + (48641377269109/10000000000000 : ℝ)*(f.failure) + (1477968564176727/100000000000000 : ℝ)*(f.sum) + (25431479410053/200000000000000000000000000000 : ℝ)*base65 + (2908950827210053/400000000000000000000000000000 : ℝ)*base67 + (2776202633210053/400000000000000000000000000000 : ℝ)*base69 + (1495785327610053/400000000000000000000000000000 : ℝ)*base71 + (284137643589947/200000000000000000000000000000 : ℝ)*base74 + (3322416227610053/400000000000000000000000000000 : ℝ)*base75 + (2595284726010053/400000000000000000000000000000 : ℝ)*base77 + (2276507396810053/400000000000000000000000000000 : ℝ)*base79 + (128408097389947/200000000000000000000000000000 : ℝ)*base82 + (6783339/500000000000000000000 : ℝ)*base90 + (6783339/500000000000000000000 : ℝ)*base92 + (6783339/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127401146683727933846073/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4668421/625000000000 : ℝ)*(base19) + (79607751/12500000000000 : ℝ)*(base23) + (21343793/50000000000000 : ℝ)*(upper2) + (145079727/100000000000000 : ℝ)*(upper3) + (21303231/25000000000000 : ℝ)*(upper5) + (258136372261569/25000000000000 : ℝ)*(major0) + (258136372261569/25000000000000 : ℝ)*(major1) + (258136372261569/25000000000000 : ℝ)*(major2) + (207035901/6250000000000 : ℝ)*(sp1) + (858008157/50000000000000 : ℝ)*(sp2) + (310748009760793/20000000000000 : ℝ)*(sp4) + (388433997320547/25000000000000 : ℝ)*(sp5) + (1553737695925643/100000000000000 : ℝ)*(sp6) + (511350844354481/100000000000000 : ℝ)*(sp7) + (511350844354481/100000000000000 : ℝ)*(f.failure) + (310748009760793/20000000000000 : ℝ)*(f.sum) + (136025351901309/50000000000000000000000000000 : ℝ)*base65 + (116524083898691/100000000000000000000000000000 : ℝ)*base68 + (782595406501309/100000000000000000000000000000 : ℝ)*base69 + (665867345001309/100000000000000000000000000000 : ℝ)*base71 + (215486052998691/50000000000000000000000000000 : ℝ)*base74 + (1315162145601309/100000000000000000000000000000 : ℝ)*base75 + (883960662101309/100000000000000000000000000000 : ℝ)*base77 + (149315226101309/100000000000000000000000000000 : ℝ)*base79 + (9322632548691/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (25757551/5000000000000000000000 : ℝ)*base90 + (25757551/5000000000000000000000 : ℝ)*base92 + (25757551/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1731_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (207/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10601/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1731_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1731_s1_0 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-267477619/2000000000 : ℝ)*x 0 + (2733233321/5000000000 : ℝ)*x 1 + (1283120133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267477619/2000000000 : ℝ)^5471 ≤ (4207584642789/50000000000000 : ℝ)^4447 := by
    have hnat : (267477619 : ℕ)^5471*50000000000000^4447 ≤ 4207584642789^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267477619 2000000000 4207584642789 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733233321/5000000000 : ℝ)^5471 ≤ (743240011059/1562500000000 : ℝ)^4447 := by
    have hnat : (2733233321 : ℕ)^5471*1562500000000^4447 ≤ 743240011059^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733233321 5000000000 743240011059 1562500000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283120133/2500000000 : ℝ)^5471 ≤ (44017469998651/100000000000000 : ℝ)^4447 := by
    have hnat : (1283120133 : ℕ)^5471*100000000000000^4447 ≤ 44017469998651^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283120133 2500000000 44017469998651 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267477619/2000000000 : ℝ), (2733233321/5000000000 : ℝ), (1283120133/2500000000 : ℝ)] ![(4207584642789/50000000000000 : ℝ), (743240011059/1562500000000 : ℝ), (44017469998651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267477619/2000000000 : ℝ)|^5471 ≤ (4207584642789/50000000000000 : ℝ)^4447
        have hw : |(-267477619/2000000000 : ℝ)|=(267477619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733233321/5000000000 : ℝ)|^5471 ≤ (743240011059/1562500000000 : ℝ)^4447
        have hw : |(2733233321/5000000000 : ℝ)|=(2733233321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1283120133/2500000000 : ℝ)|^5471 ≤ (44017469998651/100000000000000 : ℝ)^4447
        have hw : |(1283120133/2500000000 : ℝ)|=(1283120133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s1_1 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667382227/1250000000 : ℝ)*x 0 + (-302121597/2000000000 : ℝ)*x 1 + (256623981/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667382227/1250000000 : ℝ)^5471 ≤ (4620708353139/10000000000000 : ℝ)^4447 := by
    have hnat : (667382227 : ℕ)^5471*10000000000000^4447 ≤ 4620708353139^4447*1250000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667382227 1250000000 4620708353139 10000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302121597/2000000000 : ℝ)^5471 ≤ (9775456077353/100000000000000 : ℝ)^4447 := by
    have hnat : (302121597 : ℕ)^5471*100000000000000^4447 ≤ 9775456077353^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302121597 2000000000 9775456077353 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256623981/500000000 : ℝ)^5471 ≤ (5502182547007/12500000000000 : ℝ)^4447 := by
    have hnat : (256623981 : ℕ)^5471*12500000000000^4447 ≤ 5502182547007^4447*500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256623981 500000000 5502182547007 12500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667382227/1250000000 : ℝ), (-302121597/2000000000 : ℝ), (256623981/500000000 : ℝ)] ![(4620708353139/10000000000000 : ℝ), (9775456077353/100000000000000 : ℝ), (5502182547007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667382227/1250000000 : ℝ)|^5471 ≤ (4620708353139/10000000000000 : ℝ)^4447
        have hw : |(667382227/1250000000 : ℝ)|=(667382227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-302121597/2000000000 : ℝ)|^5471 ≤ (9775456077353/100000000000000 : ℝ)^4447
        have hw : |(-302121597/2000000000 : ℝ)|=(302121597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256623981/500000000 : ℝ)|^5471 ≤ (5502182547007/12500000000000 : ℝ)^4447
        have hw : |(256623981/500000000 : ℝ)|=(256623981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s1_2 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2669528183/5000000000 : ℝ)*x 0 + (641560077/1250000000 : ℝ)*x 1 + (-302121721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2669528183/5000000000 : ℝ)^5471 ≤ (23103534046331/50000000000000 : ℝ)^4447 := by
    have hnat : (2669528183 : ℕ)^5471*50000000000000^4447 ≤ 23103534046331^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669528183 5000000000 23103534046331 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641560077/1250000000 : ℝ)^5471 ≤ (22008735442471/50000000000000 : ℝ)^4447 := by
    have hnat : (641560077 : ℕ)^5471*50000000000000^4447 ≤ 22008735442471^4447*1250000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641560077 1250000000 22008735442471 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302121721/2000000000 : ℝ)^5471 ≤ (9775461013369/100000000000000 : ℝ)^4447 := by
    have hnat : (302121721 : ℕ)^5471*100000000000000^4447 ≤ 9775461013369^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302121721 2000000000 9775461013369 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2669528183/5000000000 : ℝ), (641560077/1250000000 : ℝ), (-302121721/2000000000 : ℝ)] ![(23103534046331/50000000000000 : ℝ), (22008735442471/50000000000000 : ℝ), (9775461013369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2669528183/5000000000 : ℝ)|^5471 ≤ (23103534046331/50000000000000 : ℝ)^4447
        have hw : |(2669528183/5000000000 : ℝ)|=(2669528183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641560077/1250000000 : ℝ)|^5471 ≤ (22008735442471/50000000000000 : ℝ)^4447
        have hw : |(641560077/1250000000 : ℝ)|=(641560077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302121721/2000000000 : ℝ)|^5471 ≤ (9775461013369/100000000000000 : ℝ)^4447
        have hw : |(-302121721/2000000000 : ℝ)|=(302121721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s1_3 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4076861513/10000000000 : ℝ)*x 0 + (897094011/2500000000 : ℝ)*x 1 + (4603188003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4076861513/10000000000 : ℝ)^5471 ≤ (207241473661/625000000000 : ℝ)^4447 := by
    have hnat : (4076861513 : ℕ)^5471*625000000000^4447 ≤ 207241473661^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4076861513 10000000000 207241473661 625000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897094011/2500000000 : ℝ)^5471 ≤ (3542545053799/12500000000000 : ℝ)^4447 := by
    have hnat : (897094011 : ℕ)^5471*12500000000000^4447 ≤ 3542545053799^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897094011 2500000000 3542545053799 12500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4603188003/10000000000 : ℝ)^5471 ≤ (1203156368197/3125000000000 : ℝ)^4447 := by
    have hnat : (4603188003 : ℕ)^5471*3125000000000^4447 ≤ 1203156368197^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4603188003 10000000000 1203156368197 3125000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4076861513/10000000000 : ℝ), (897094011/2500000000 : ℝ), (4603188003/10000000000 : ℝ)] ![(207241473661/625000000000 : ℝ), (3542545053799/12500000000000 : ℝ), (1203156368197/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4076861513/10000000000 : ℝ)|^5471 ≤ (207241473661/625000000000 : ℝ)^4447
        have hw : |(4076861513/10000000000 : ℝ)|=(4076861513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897094011/2500000000 : ℝ)|^5471 ≤ (3542545053799/12500000000000 : ℝ)^4447
        have hw : |(897094011/2500000000 : ℝ)|=(897094011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4603188003/10000000000 : ℝ)|^5471 ≤ (1203156368197/3125000000000 : ℝ)^4447
        have hw : |(4603188003/10000000000 : ℝ)|=(4603188003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s1_4 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-334388469/2500000000 : ℝ)*x 0 + (1027290531/2000000000 : ℝ)*x 1 + (2731215597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334388469/2500000000 : ℝ)^5471 ≤ (4208226319011/50000000000000 : ℝ)^4447 := by
    have hnat : (334388469 : ℕ)^5471*50000000000000^4447 ≤ 4208226319011^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334388469 2500000000 4208226319011 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027290531/2000000000 : ℝ)^5471 ≤ (44059383961863/100000000000000 : ℝ)^4447 := by
    have hnat : (1027290531 : ℕ)^5471*100000000000000^4447 ≤ 44059383961863^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027290531 2000000000 44059383961863 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731215597/5000000000 : ℝ)^5471 ≤ (5940520423857/12500000000000 : ℝ)^4447 := by
    have hnat : (2731215597 : ℕ)^5471*12500000000000^4447 ≤ 5940520423857^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731215597 5000000000 5940520423857 12500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-334388469/2500000000 : ℝ), (1027290531/2000000000 : ℝ), (2731215597/5000000000 : ℝ)] ![(4208226319011/50000000000000 : ℝ), (44059383961863/100000000000000 : ℝ), (5940520423857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-334388469/2500000000 : ℝ)|^5471 ≤ (4208226319011/50000000000000 : ℝ)^4447
        have hw : |(-334388469/2500000000 : ℝ)|=(334388469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027290531/2000000000 : ℝ)|^5471 ≤ (44059383961863/100000000000000 : ℝ)^4447
        have hw : |(1027290531/2000000000 : ℝ)|=(1027290531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731215597/5000000000 : ℝ)|^5471 ≤ (5940520423857/12500000000000 : ℝ)^4447
        have hw : |(2731215597/5000000000 : ℝ)|=(2731215597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s1_5 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2624829187/5000000000 : ℝ)*x 0 + (-1180657783/10000000000 : ℝ)*x 1 + (5462430627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624829187/5000000000 : ℝ)^5471 ≤ (45257055030689/100000000000000 : ℝ)^4447 := by
    have hnat : (2624829187 : ℕ)^5471*100000000000000^4447 ≤ 45257055030689^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624829187 5000000000 45257055030689 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1180657783/10000000000 : ℝ)^5471 ≤ (1443757528631/20000000000000 : ℝ)^4447 := by
    have hnat : (1180657783 : ℕ)^5471*20000000000000^4447 ≤ 1443757528631^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180657783 10000000000 1443757528631 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462430627/10000000000 : ℝ)^5471 ≤ (2376207866097/5000000000000 : ℝ)^4447 := by
    have hnat : (5462430627 : ℕ)^5471*5000000000000^4447 ≤ 2376207866097^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462430627 10000000000 2376207866097 5000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624829187/5000000000 : ℝ), (-1180657783/10000000000 : ℝ), (5462430627/10000000000 : ℝ)] ![(45257055030689/100000000000000 : ℝ), (1443757528631/20000000000000 : ℝ), (2376207866097/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624829187/5000000000 : ℝ)|^5471 ≤ (45257055030689/100000000000000 : ℝ)^4447
        have hw : |(2624829187/5000000000 : ℝ)|=(2624829187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1180657783/10000000000 : ℝ)|^5471 ≤ (1443757528631/20000000000000 : ℝ)^4447
        have hw : |(-1180657783/10000000000 : ℝ)|=(1180657783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462430627/10000000000 : ℝ)|^5471 ≤ (2376207866097/5000000000000 : ℝ)^4447
        have hw : |(5462430627/10000000000 : ℝ)|=(5462430627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s1_6 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164051823/312500000 : ℝ)*x 0 + (5462430373/10000000000 : ℝ)*x 1 + (-295164549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164051823/312500000 : ℝ)^5471 ≤ (22628527313829/50000000000000 : ℝ)^4447 := by
    have hnat : (164051823 : ℕ)^5471*50000000000000^4447 ≤ 22628527313829^4447*312500000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164051823 312500000 22628527313829 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462430373/10000000000 : ℝ)^5471 ≤ (47524154603237/100000000000000 : ℝ)^4447 := by
    have hnat : (5462430373 : ℕ)^5471*100000000000000^4447 ≤ 47524154603237^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462430373 10000000000 47524154603237 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (295164549/2500000000 : ℝ)^5471 ≤ (7218790749787/100000000000000 : ℝ)^4447 := by
    have hnat : (295164549 : ℕ)^5471*100000000000000^4447 ≤ 7218790749787^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295164549 2500000000 7218790749787 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164051823/312500000 : ℝ), (5462430373/10000000000 : ℝ), (-295164549/2500000000 : ℝ)] ![(22628527313829/50000000000000 : ℝ), (47524154603237/100000000000000 : ℝ), (7218790749787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164051823/312500000 : ℝ)|^5471 ≤ (22628527313829/50000000000000 : ℝ)^4447
        have hw : |(164051823/312500000 : ℝ)|=(164051823/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462430373/10000000000 : ℝ)|^5471 ≤ (47524154603237/100000000000000 : ℝ)^4447
        have hw : |(5462430373/10000000000 : ℝ)|=(5462430373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-295164549/2500000000 : ℝ)|^5471 ≤ (7218790749787/100000000000000 : ℝ)^4447
        have hw : |(-295164549/2500000000 : ℝ)|=(295164549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s1_7 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4077361109/10000000000 : ℝ)*x 0 + (1147779493/2500000000 : ℝ)*x 1 + (900158829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4077361109/10000000000 : ℝ)^5471 ≤ (259090897863/781250000000 : ℝ)^4447 := by
    have hnat : (4077361109 : ℕ)^5471*781250000000^4447 ≤ 259090897863^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4077361109 10000000000 259090897863 781250000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147779493/2500000000 : ℝ)^5471 ≤ (38376841384179/100000000000000 : ℝ)^4447 := by
    have hnat : (1147779493 : ℕ)^5471*100000000000000^4447 ≤ 38376841384179^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147779493 2500000000 38376841384179 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900158829/2500000000 : ℝ)^5471 ≤ (28459523677753/100000000000000 : ℝ)^4447 := by
    have hnat : (900158829 : ℕ)^5471*100000000000000^4447 ≤ 28459523677753^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900158829 2500000000 28459523677753 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4077361109/10000000000 : ℝ), (1147779493/2500000000 : ℝ), (900158829/2500000000 : ℝ)] ![(259090897863/781250000000 : ℝ), (38376841384179/100000000000000 : ℝ), (28459523677753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4077361109/10000000000 : ℝ)|^5471 ≤ (259090897863/781250000000 : ℝ)^4447
        have hw : |(4077361109/10000000000 : ℝ)|=(4077361109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147779493/2500000000 : ℝ)|^5471 ≤ (38376841384179/100000000000000 : ℝ)^4447
        have hw : |(1147779493/2500000000 : ℝ)|=(1147779493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900158829/2500000000 : ℝ)|^5471 ≤ (28459523677753/100000000000000 : ℝ)^4447
        have hw : |(900158829/2500000000 : ℝ)|=(900158829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1731_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10601/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (9987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8571/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10601/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (207/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10601/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (207/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10601/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (207/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10601/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (207/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10601/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (207/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10601/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (207/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (207/3125 : ℝ) ^ (5463/1024 : ℝ) ≤ (1284289660023/2500000000000000000 : ℝ) := by
    have hpowers : (207/3125 : ℝ)^5463 ≤ (1284289660023/2500000000000000000 : ℝ)^1024 := by
      have hnat : (207 : ℕ)^5463*2500000000000000000^1024 ≤ 1284289660023^1024*3125^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        207 3125 1284289660023 2500000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (207/3125 : ℝ)) (X := (1284289660023/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10601/50000 : ℝ) ^ (5463/1024 : ℝ) ≤ (3185346748400299/12500000000000000000 : ℝ) := by
    have hpowers : (10601/50000 : ℝ)^5463 ≤ (3185346748400299/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10601 : ℕ)^5463*12500000000000000000^1024 ≤ 3185346748400299^1024*50000^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10601 50000 3185346748400299 12500000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10601/50000 : ℝ)) (X := (3185346748400299/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250001284289660023/1250000000000000000 : ℝ) ≤ (2000000385169193/2000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (1250001284289660023/1250000000000000000 : ℝ)^1024 ≤ (2000000385169193/2000000000000000 : ℝ)^5463 := by
      have hnat : (1250001284289660023 : ℕ)^1024*2000000000000000^5463 ≤ 2000000385169193^5463*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250001284289660023 1250000000000000000 2000000385169193 2000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000385169193/2000000000000000 : ℝ)) (X := (1250001284289660023/1250000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251595884098350207/6250000000000000000 : ℝ) ≤ (1250059821190293/1250000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (6251595884098350207/6250000000000000000 : ℝ)^1024 ≤ (1250059821190293/1250000000000000 : ℝ)^5463 := by
      have hnat : (6251595884098350207 : ℕ)^1024*1250000000000000^5463 ≤ 1250059821190293^5463*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251595884098350207 6250000000000000000 1250059821190293 1250000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250059821190293/1250000000000000 : ℝ)) (X := (6251595884098350207/6250000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253185346748400299/6250000000000000000 : ℝ) ≤ (10000955213198723/10000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (6253185346748400299/6250000000000000000 : ℝ)^1024 ≤ (10000955213198723/10000000000000000 : ℝ)^5463 := by
      have hnat : (6253185346748400299 : ℕ)^1024*10000000000000000^5463 ≤ 10000955213198723^5463*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253185346748400299 6250000000000000000 10000955213198723 10000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000955213198723/10000000000000000 : ℝ)) (X := (6253185346748400299/6250000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1284289660023/2500000000000000000 : ℝ) ≤ ((72886856749778904389/72890000000000000000 : ℝ)+2*(476643676379/1457800000000000 : ℝ)*(207/3125 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (72886856749778904389/72890000000000000000 : ℝ)+2*(476643676379/1457800000000000 : ℝ)*(207/3125 : ℝ)=(2000000385169193/2000000000000000 : ℝ) by norm_num, show 1+2*(1284289660023/2500000000000000000 : ℝ)=(1250001284289660023/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3185346748400299/12500000000000000000 : ℝ)+(1284289660023/2500000000000000000 : ℝ) ≤ ((72886856749778904389/72890000000000000000 : ℝ)+(476643676379/1457800000000000 : ℝ)*((10601/50000 : ℝ)+(207/3125 : ℝ)))^(5463/1024 : ℝ) := by
    rw [show (72886856749778904389/72890000000000000000 : ℝ)+(476643676379/1457800000000000 : ℝ)*((10601/50000 : ℝ)+(207/3125 : ℝ))=(1250059821190293/1250000000000000 : ℝ) by norm_num, show 1+(3185346748400299/12500000000000000000 : ℝ)+(1284289660023/2500000000000000000 : ℝ)=(6251595884098350207/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3185346748400299/12500000000000000000 : ℝ) ≤ ((72886856749778904389/72890000000000000000 : ℝ)+2*(476643676379/1457800000000000 : ℝ)*(10601/50000 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (72886856749778904389/72890000000000000000 : ℝ)+2*(476643676379/1457800000000000 : ℝ)*(10601/50000 : ℝ)=(10000955213198723/10000000000000000 : ℝ) by norm_num, show 1+2*(3185346748400299/12500000000000000000 : ℝ)=(6253185346748400299/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72886856749778904389/72890000000000000000 : ℝ)*(X 1 0+X 2 0)+(476643676379/1457800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (207/3125 : ℝ)) (hi := (10601/50000 : ℝ)) (c := (72886856749778904389/72890000000000000000 : ℝ)) (alpha := (476643676379/1457800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72886856749778904389/72890000000000000000 : ℝ)*(X 0 1+X 2 1)+(476643676379/1457800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (207/3125 : ℝ)) (hi := (10601/50000 : ℝ)) (c := (72886856749778904389/72890000000000000000 : ℝ)) (alpha := (476643676379/1457800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72886856749778904389/72890000000000000000 : ℝ)*(X 0 2+X 1 2)+(476643676379/1457800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (207/3125 : ℝ)) (hi := (10601/50000 : ℝ)) (c := (72886856749778904389/72890000000000000000 : ℝ)) (alpha := (476643676379/1457800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-267477619/2000000000 : ℝ)*X 0 0+(2733233321/5000000000 : ℝ)*X 0 1+(1283120133/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((667382227/1250000000 : ℝ)*X 1 0+(-302121597/2000000000 : ℝ)*X 1 1+(256623981/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2669528183/5000000000 : ℝ)*X 2 0+(641560077/1250000000 : ℝ)*X 2 1+(-302121721/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4076861513/10000000000 : ℝ)*X 0 0+(897094011/2500000000 : ℝ)*X 0 1+(4603188003/10000000000 : ℝ)*X 0 2+(4076861513/10000000000 : ℝ)*X 1 0+(897094011/2500000000 : ℝ)*X 1 1+(4603188003/10000000000 : ℝ)*X 1 2+(4076861513/10000000000 : ℝ)*X 2 0+(897094011/2500000000 : ℝ)*X 2 1+(4603188003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-334388469/2500000000 : ℝ)*X 0 0+(1027290531/2000000000 : ℝ)*X 0 1+(2731215597/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2624829187/5000000000 : ℝ)*X 1 0+(-1180657783/10000000000 : ℝ)*X 1 1+(5462430627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((164051823/312500000 : ℝ)*X 2 0+(5462430373/10000000000 : ℝ)*X 2 1+(-295164549/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4077361109/10000000000 : ℝ)*X 0 0+(1147779493/2500000000 : ℝ)*X 0 1+(900158829/2500000000 : ℝ)*X 0 2+(4077361109/10000000000 : ℝ)*X 1 0+(1147779493/2500000000 : ℝ)*X 1 1+(900158829/2500000000 : ℝ)*X 1 2+(4077361109/10000000000 : ℝ)*X 2 0+(1147779493/2500000000 : ℝ)*X 2 1+(900158829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53078452359021490524057/7289000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1018845077/100000000000000 : ℝ)*(base19) + (340177357/100000000000000 : ℝ)*(base23) + (13880891/25000000000000 : ℝ)*(lower2) + (165346917/100000000000000 : ℝ)*(lower4) + (5027161/10000000000000 : ℝ)*(lower5) + (198978001041051/10000000000000 : ℝ)*(major0) + (198978001041051/10000000000000 : ℝ)*(major1) + (198978001041051/10000000000000 : ℝ)*(major2) + (5988295658727/200000000000 : ℝ)*(sp0) + (1497076782400781/50000000000000 : ℝ)*(sp1) + (1497074995535269/50000000000000 : ℝ)*(sp2) + (246351298610313/25000000000000 : ℝ)*(sp3) + (3377141569/50000000000000 : ℝ)*(sp4) + (531549843/12500000000000 : ℝ)*(sp6) + (246351298610313/25000000000000 : ℝ)*(f.failure) + (1497077291823319/50000000000000 : ℝ)*(f.sum) + (73469720199697/7289000000000000000000000000 : ℝ)*base65 + (1005961415004677161/728900000000000000000000000000000 : ℝ)*base68 + (1530375113850322839/728900000000000000000000000000000 : ℝ)*base69 + (1309405915424322839/728900000000000000000000000000000 : ℝ)*base71 + (10259282507373/7289000000000000000000000000 : ℝ)*base74 + (4656803368354877161/728900000000000000000000000000000 : ℝ)*base76 + (278474319354322839/728900000000000000000000000000000 : ℝ)*base77 + (322358562921677161/728900000000000000000000000000000 : ℝ)*base80 + (8230899033409/7289000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10961577/1250000000000000000000 : ℝ)*base89 + (10961577/1250000000000000000000 : ℝ)*base91 + (10961577/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1004240751398498319703524561/182225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1127683571/100000000000000 : ℝ)*(base19) + (1395153071/100000000000000 : ℝ)*(base23) + (39844571/20000000000000 : ℝ)*(upper2) + (2001827/50000000000000 : ℝ)*(upper3) + (40816857/12500000000000 : ℝ)*(upper5) + (101932408834939/5000000000000 : ℝ)*(major0) + (101932408834939/5000000000000 : ℝ)*(major1) + (101932408834939/5000000000000 : ℝ)*(major2) + (5057608083/50000000000000 : ℝ)*(sp1) + (4840842669/100000000000000 : ℝ)*(sp2) + (1533844917552339/50000000000000 : ℝ)*(sp4) + (153383929610247/5000000000000 : ℝ)*(sp5) + (3067683599108937/100000000000000 : ℝ)*(sp6) + (504803167296547/50000000000000 : ℝ)*(sp7) + (504803167296547/50000000000000 : ℝ)*(f.failure) + (1533844917552339/50000000000000 : ℝ)*(f.sum) + (726242058357/364450000000000000000000000 : ℝ)*base66 + (2425483493489597271/364450000000000000000000000000000 : ℝ)*base67 + (926599854797497271/364450000000000000000000000000000 : ℝ)*base69 + (2965636003271797271/364450000000000000000000000000000 : ℝ)*base71 + (1687582263229/364450000000000000000000000 : ℝ)*base73 + (3753380194299897271/364450000000000000000000000000000 : ℝ)*base75 + (773101643490297271/364450000000000000000000000000000 : ℝ)*base77 + (5546368150647847271/364450000000000000000000000000000 : ℝ)*base79 + (20696393652961/7289000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21912637/2500000000000000000000 : ℝ)*base90 + (21912637/2500000000000000000000 : ℝ)*base92 + (21912637/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1731_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10601/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1731_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1731_s2_0 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1339609991/10000000000 : ℝ)*x 0 + (5457216369/10000000000 : ℝ)*x 1 + (1028046483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339609991/10000000000 : ℝ)^5471 ≤ (8432372584867/100000000000000 : ℝ)^4447 := by
    have hnat : (1339609991 : ℕ)^5471*100000000000000^4447 ≤ 8432372584867^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339609991 10000000000 8432372584867 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457216369/10000000000 : ℝ)^5471 ≤ (47468352356013/100000000000000 : ℝ)^4447 := by
    have hnat : (5457216369 : ℕ)^5471*100000000000000^4447 ≤ 47468352356013^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457216369 10000000000 47468352356013 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028046483/2000000000 : ℝ)^5471 ≤ (2756204689733/6250000000000 : ℝ)^4447 := by
    have hnat : (1028046483 : ℕ)^5471*6250000000000^4447 ≤ 2756204689733^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028046483 2000000000 2756204689733 6250000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1339609991/10000000000 : ℝ), (5457216369/10000000000 : ℝ), (1028046483/2000000000 : ℝ)] ![(8432372584867/100000000000000 : ℝ), (47468352356013/100000000000000 : ℝ), (2756204689733/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1339609991/10000000000 : ℝ)|^5471 ≤ (8432372584867/100000000000000 : ℝ)^4447
        have hw : |(-1339609991/10000000000 : ℝ)|=(1339609991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457216369/10000000000 : ℝ)|^5471 ≤ (47468352356013/100000000000000 : ℝ)^4447
        have hw : |(5457216369/10000000000 : ℝ)|=(5457216369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028046483/2000000000 : ℝ)|^5471 ≤ (2756204689733/6250000000000 : ℝ)^4447
        have hw : |(1028046483/2000000000 : ℝ)|=(1028046483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s2_1 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5336528381/10000000000 : ℝ)*x 0 + (-751855437/5000000000 : ℝ)*x 1 + (2570116063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5336528381/10000000000 : ℝ)^5471 ≤ (9236030619501/20000000000000 : ℝ)^4447 := by
    have hnat : (5336528381 : ℕ)^5471*20000000000000^4447 ≤ 9236030619501^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336528381 10000000000 9236030619501 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (751855437/5000000000 : ℝ)^5471 ≤ (9720574899061/100000000000000 : ℝ)^4447 := by
    have hnat : (751855437 : ℕ)^5471*100000000000000^4447 ≤ 9720574899061^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751855437 5000000000 9720574899061 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570116063/5000000000 : ℝ)^5471 ≤ (44099271985403/100000000000000 : ℝ)^4447 := by
    have hnat : (2570116063 : ℕ)^5471*100000000000000^4447 ≤ 44099271985403^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570116063 5000000000 44099271985403 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5336528381/10000000000 : ℝ), (-751855437/5000000000 : ℝ), (2570116063/5000000000 : ℝ)] ![(9236030619501/20000000000000 : ℝ), (9720574899061/100000000000000 : ℝ), (44099271985403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5336528381/10000000000 : ℝ)|^5471 ≤ (9236030619501/20000000000000 : ℝ)^4447
        have hw : |(5336528381/10000000000 : ℝ)|=(5336528381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-751855437/5000000000 : ℝ)|^5471 ≤ (9720574899061/100000000000000 : ℝ)^4447
        have hw : |(-751855437/5000000000 : ℝ)|=(751855437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570116063/5000000000 : ℝ)|^5471 ≤ (44099271985403/100000000000000 : ℝ)^4447
        have hw : |(2570116063/5000000000 : ℝ)|=(2570116063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s2_2 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334132019/2500000000 : ℝ)*x 0 + (321264527/625000000 : ℝ)*x 1 + (-1503710877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334132019/2500000000 : ℝ)^5471 ≤ (23090074925201/50000000000000 : ℝ)^4447 := by
    have hnat : (1334132019 : ℕ)^5471*50000000000000^4447 ≤ 23090074925201^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334132019 2500000000 23090074925201 50000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321264527/625000000 : ℝ)^5471 ≤ (44099275215159/100000000000000 : ℝ)^4447 := by
    have hnat : (321264527 : ℕ)^5471*100000000000000^4447 ≤ 44099275215159^4447*625000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321264527 625000000 44099275215159 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503710877/10000000000 : ℝ)^5471 ≤ (243014373073/2500000000000 : ℝ)^4447 := by
    have hnat : (1503710877 : ℕ)^5471*2500000000000^4447 ≤ 243014373073^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503710877 10000000000 243014373073 2500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334132019/2500000000 : ℝ), (321264527/625000000 : ℝ), (-1503710877/10000000000 : ℝ)] ![(23090074925201/50000000000000 : ℝ), (44099275215159/100000000000000 : ℝ), (243014373073/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334132019/2500000000 : ℝ)|^5471 ≤ (23090074925201/50000000000000 : ℝ)^4447
        have hw : |(1334132019/2500000000 : ℝ)|=(1334132019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321264527/625000000 : ℝ)|^5471 ≤ (44099275215159/100000000000000 : ℝ)^4447
        have hw : |(321264527/625000000 : ℝ)|=(321264527/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1503710877/10000000000 : ℝ)|^5471 ≤ (243014373073/2500000000000 : ℝ)^4447
        have hw : |(-1503710877/10000000000 : ℝ)|=(1503710877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s2_3 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (101964861/250000000 : ℝ)*x 0 + (903514517/2500000000 : ℝ)*x 1 + (2288607641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101964861/250000000 : ℝ)^5471 ≤ (8293994173101/25000000000000 : ℝ)^4447 := by
    have hnat : (101964861 : ℕ)^5471*25000000000000^4447 ≤ 8293994173101^4447*250000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101964861 250000000 8293994173101 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903514517/2500000000 : ℝ)^5471 ≤ (28590103425539/100000000000000 : ℝ)^4447 := by
    have hnat : (903514517 : ℕ)^5471*100000000000000^4447 ≤ 28590103425539^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903514517 2500000000 28590103425539 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2288607641/5000000000 : ℝ)^5471 ≤ (38233919859579/100000000000000 : ℝ)^4447 := by
    have hnat : (2288607641 : ℕ)^5471*100000000000000^4447 ≤ 38233919859579^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288607641 5000000000 38233919859579 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(101964861/250000000 : ℝ), (903514517/2500000000 : ℝ), (2288607641/5000000000 : ℝ)] ![(8293994173101/25000000000000 : ℝ), (28590103425539/100000000000000 : ℝ), (38233919859579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(101964861/250000000 : ℝ)|^5471 ≤ (8293994173101/25000000000000 : ℝ)^4447
        have hw : |(101964861/250000000 : ℝ)|=(101964861/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903514517/2500000000 : ℝ)|^5471 ≤ (28590103425539/100000000000000 : ℝ)^4447
        have hw : |(903514517/2500000000 : ℝ)|=(903514517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2288607641/5000000000 : ℝ)|^5471 ≤ (38233919859579/100000000000000 : ℝ)^4447
        have hw : |(2288607641/5000000000 : ℝ)|=(2288607641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s2_4 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-334937687/2500000000 : ℝ)*x 0 + (1285953089/2500000000 : ℝ)*x 1 + (1090716599/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334937687/2500000000 : ℝ)^5471 ≤ (2108365658611/25000000000000 : ℝ)^4447 := by
    have hnat : (334937687 : ℕ)^5471*25000000000000^4447 ≤ 2108365658611^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334937687 2500000000 2108365658611 25000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285953089/2500000000 : ℝ)^5471 ≤ (44137063475859/100000000000000 : ℝ)^4447 := by
    have hnat : (1285953089 : ℕ)^5471*100000000000000^4447 ≤ 44137063475859^4447*2500000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285953089 2500000000 44137063475859 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090716599/2000000000 : ℝ)^5471 ≤ (47429473867193/100000000000000 : ℝ)^4447 := by
    have hnat : (1090716599 : ℕ)^5471*100000000000000^4447 ≤ 47429473867193^4447*2000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090716599 2000000000 47429473867193 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-334937687/2500000000 : ℝ), (1285953089/2500000000 : ℝ), (1090716599/2000000000 : ℝ)] ![(2108365658611/25000000000000 : ℝ), (44137063475859/100000000000000 : ℝ), (47429473867193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-334937687/2500000000 : ℝ)|^5471 ≤ (2108365658611/25000000000000 : ℝ)^4447
        have hw : |(-334937687/2500000000 : ℝ)|=(334937687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285953089/2500000000 : ℝ)|^5471 ≤ (44137063475859/100000000000000 : ℝ)^4447
        have hw : |(1285953089/2500000000 : ℝ)|=(1285953089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090716599/2000000000 : ℝ)|^5471 ≤ (47429473867193/100000000000000 : ℝ)^4447
        have hw : |(1090716599/2000000000 : ℝ)|=(1090716599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s2_5 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251697901/10000000000 : ℝ)*x 0 + (-148795013/1250000000 : ℝ)*x 1 + (5453583017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251697901/10000000000 : ℝ)^5471 ≤ (9055737476287/20000000000000 : ℝ)^4447 := by
    have hnat : (5251697901 : ℕ)^5471*20000000000000^4447 ≤ 9055737476287^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251697901 10000000000 9055737476287 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148795013/1250000000 : ℝ)^5471 ≤ (7291838497941/100000000000000 : ℝ)^4447 := by
    have hnat : (148795013 : ℕ)^5471*100000000000000^4447 ≤ 7291838497941^4447*1250000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148795013 1250000000 7291838497941 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453583017/10000000000 : ℝ)^5471 ≤ (47429474102583/100000000000000 : ℝ)^4447 := by
    have hnat : (5453583017 : ℕ)^5471*100000000000000^4447 ≤ 47429474102583^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453583017 10000000000 47429474102583 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251697901/10000000000 : ℝ), (-148795013/1250000000 : ℝ), (5453583017/10000000000 : ℝ)] ![(9055737476287/20000000000000 : ℝ), (7291838497941/100000000000000 : ℝ), (47429474102583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251697901/10000000000 : ℝ)|^5471 ≤ (9055737476287/20000000000000 : ℝ)^4447
        have hw : |(5251697901/10000000000 : ℝ)|=(5251697901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-148795013/1250000000 : ℝ)|^5471 ≤ (7291838497941/100000000000000 : ℝ)^4447
        have hw : |(-148795013/1250000000 : ℝ)|=(148795013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453583017/10000000000 : ℝ)|^5471 ≤ (47429474102583/100000000000000 : ℝ)^4447
        have hw : |(5453583017/10000000000 : ℝ)|=(5453583017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s2_6 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525169783/1000000000 : ℝ)*x 0 + (2726791541/5000000000 : ℝ)*x 1 + (-1190360111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525169783/1000000000 : ℝ)^5471 ≤ (2829917914271/6250000000000 : ℝ)^4447 := by
    have hnat : (525169783 : ℕ)^5471*6250000000000^4447 ≤ 2829917914271^4447*1000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525169783 1000000000 2829917914271 6250000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726791541/5000000000 : ℝ)^5471 ≤ (9485894959611/20000000000000 : ℝ)^4447 := by
    have hnat : (2726791541 : ℕ)^5471*20000000000000^4447 ≤ 9485894959611^4447*5000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726791541 5000000000 9485894959611 20000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190360111/10000000000 : ℝ)^5471 ≤ (911479818837/12500000000000 : ℝ)^4447 := by
    have hnat : (1190360111 : ℕ)^5471*12500000000000^4447 ≤ 911479818837^4447*10000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190360111 10000000000 911479818837 12500000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525169783/1000000000 : ℝ), (2726791541/5000000000 : ℝ), (-1190360111/10000000000 : ℝ)] ![(2829917914271/6250000000000 : ℝ), (9485894959611/20000000000000 : ℝ), (911479818837/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525169783/1000000000 : ℝ)|^5471 ≤ (2829917914271/6250000000000 : ℝ)^4447
        have hw : |(525169783/1000000000 : ℝ)|=(525169783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726791541/5000000000 : ℝ)|^5471 ≤ (9485894959611/20000000000000 : ℝ)^4447
        have hw : |(2726791541/5000000000 : ℝ)|=(2726791541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1190360111/10000000000 : ℝ)|^5471 ≤ (911479818837/12500000000000 : ℝ)^4447
        have hw : |(-1190360111/10000000000 : ℝ)|=(1190360111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1731_s2_7 (p : ℝ) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (50987769/125000000 : ℝ)*x 0 + (182653473/400000000 : ℝ)*x 1 + (362509857/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50987769/125000000 : ℝ)^5471 ≤ (265442004967/800000000000 : ℝ)^4447 := by
    have hnat : (50987769 : ℕ)^5471*800000000000^4447 ≤ 265442004967^4447*125000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50987769 125000000 265442004967 800000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182653473/400000000 : ℝ)^5471 ≤ (38122157530223/100000000000000 : ℝ)^4447 := by
    have hnat : (182653473 : ℕ)^5471*100000000000000^4447 ≤ 38122157530223^4447*400000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182653473 400000000 38122157530223 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362509857/1000000000 : ℝ)^5471 ≤ (28697591828381/100000000000000 : ℝ)^4447 := by
    have hnat : (362509857 : ℕ)^5471*100000000000000^4447 ≤ 28697591828381^4447*1000000000^5471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362509857 1000000000 28697591828381 100000000000000 5471 4447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5471/1024 : ℝ)) 5471 4447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50987769/125000000 : ℝ), (182653473/400000000 : ℝ), (362509857/1000000000 : ℝ)] ![(265442004967/800000000000 : ℝ), (38122157530223/100000000000000 : ℝ), (28697591828381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50987769/125000000 : ℝ)|^5471 ≤ (265442004967/800000000000 : ℝ)^4447
        have hw : |(50987769/125000000 : ℝ)|=(50987769/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182653473/400000000 : ℝ)|^5471 ≤ (38122157530223/100000000000000 : ℝ)^4447
        have hw : |(182653473/400000000 : ℝ)|=(182653473/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362509857/1000000000 : ℝ)|^5471 ≤ (28697591828381/100000000000000 : ℝ)^4447
        have hw : |(362509857/1000000000 : ℝ)|=(362509857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1731_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2539/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16947/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8571/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8571/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8571/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8571/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8571/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8571/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9987/100000 : ℝ) ^ (5463/1024 : ℝ) ≤ (114806131790457/25000000000000000000 : ℝ) := by
    have hpowers : (9987/100000 : ℝ)^5463 ≤ (114806131790457/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9987 : ℕ)^5463*25000000000000000000^1024 ≤ 114806131790457^1024*100000^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9987 100000 114806131790457 25000000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9987/100000 : ℝ)) (X := (114806131790457/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8571/50000 : ℝ) ^ (5463/1024 : ℝ) ≤ (4099378103611991/50000000000000000000 : ℝ) := by
    have hpowers : (8571/50000 : ℝ)^5463 ≤ (4099378103611991/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8571 : ℕ)^5463*50000000000000000000^1024 ≤ 4099378103611991^1024*50000^5463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8571 50000 4099378103611991 50000000000000000000 5463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8571/50000 : ℝ)) (X := (4099378103611991/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500114806131790457/12500000000000000000 : ℝ) ≤ (5000008607800863/5000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (12500114806131790457/12500000000000000000 : ℝ)^1024 ≤ (5000008607800863/5000000000000000 : ℝ)^5463 := by
      have hnat : (12500114806131790457 : ℕ)^1024*5000000000000000^5463 ≤ 5000008607800863^5463*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500114806131790457 12500000000000000000 5000008607800863 5000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000008607800863/5000000000000000 : ℝ)) (X := (12500114806131790457/12500000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10000865798073438581/10000000000000000000 : ℝ) ≤ (2500040570476067/2500000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (10000865798073438581/10000000000000000000 : ℝ)^1024 ≤ (2500040570476067/2500000000000000 : ℝ)^5463 := by
      have hnat : (10000865798073438581 : ℕ)^1024*2500000000000000^5463 ≤ 2500040570476067^5463*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000865798073438581 10000000000000000000 2500040570476067 2500000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500040570476067/2500000000000000 : ℝ)) (X := (10000865798073438581/10000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004099378103611991/25000000000000000000 : ℝ) ≤ (1000030734820681/1000000000000000 : ℝ) ^ (5463/1024 : ℝ) := by
    have hpowers : (25004099378103611991/25000000000000000000 : ℝ)^1024 ≤ (1000030734820681/1000000000000000 : ℝ)^5463 := by
      have hnat : (25004099378103611991 : ℕ)^1024*1000000000000000^5463 ≤ 1000030734820681^5463*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004099378103611991 25000000000000000000 1000030734820681 1000000000000000 1024 5463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000030734820681/1000000000000000 : ℝ)) (X := (25004099378103611991/25000000000000000000 : ℝ)) (by norm_num) 5463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(114806131790457/25000000000000000000 : ℝ) ≤ ((11924537603883895937/11925000000000000000 : ℝ)+2*(72533151271/357750000000000 : ℝ)*(9987/100000 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (11924537603883895937/11925000000000000000 : ℝ)+2*(72533151271/357750000000000 : ℝ)*(9987/100000 : ℝ)=(5000008607800863/5000000000000000 : ℝ) by norm_num, show 1+2*(114806131790457/25000000000000000000 : ℝ)=(12500114806131790457/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4099378103611991/50000000000000000000 : ℝ)+(114806131790457/25000000000000000000 : ℝ) ≤ ((11924537603883895937/11925000000000000000 : ℝ)+(72533151271/357750000000000 : ℝ)*((8571/50000 : ℝ)+(9987/100000 : ℝ)))^(5463/1024 : ℝ) := by
    rw [show (11924537603883895937/11925000000000000000 : ℝ)+(72533151271/357750000000000 : ℝ)*((8571/50000 : ℝ)+(9987/100000 : ℝ))=(2500040570476067/2500000000000000 : ℝ) by norm_num, show 1+(4099378103611991/50000000000000000000 : ℝ)+(114806131790457/25000000000000000000 : ℝ)=(10000865798073438581/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4099378103611991/50000000000000000000 : ℝ) ≤ ((11924537603883895937/11925000000000000000 : ℝ)+2*(72533151271/357750000000000 : ℝ)*(8571/50000 : ℝ))^(5463/1024 : ℝ) := by
    rw [show (11924537603883895937/11925000000000000000 : ℝ)+2*(72533151271/357750000000000 : ℝ)*(8571/50000 : ℝ)=(1000030734820681/1000000000000000 : ℝ) by norm_num, show 1+2*(4099378103611991/50000000000000000000 : ℝ)=(25004099378103611991/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11924537603883895937/11925000000000000000 : ℝ)*(X 1 0+X 2 0)+(72533151271/357750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (9987/100000 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (11924537603883895937/11925000000000000000 : ℝ)) (alpha := (72533151271/357750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11924537603883895937/11925000000000000000 : ℝ)*(X 0 1+X 2 1)+(72533151271/357750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (9987/100000 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (11924537603883895937/11925000000000000000 : ℝ)) (alpha := (72533151271/357750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11924537603883895937/11925000000000000000 : ℝ)*(X 0 2+X 1 2)+(72533151271/357750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5463/1024 : ℝ)) (lo := (9987/100000 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (11924537603883895937/11925000000000000000 : ℝ)) (alpha := (72533151271/357750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1339609991/10000000000 : ℝ)*X 0 0+(5457216369/10000000000 : ℝ)*X 0 1+(1028046483/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5336528381/10000000000 : ℝ)*X 1 0+(-751855437/5000000000 : ℝ)*X 1 1+(2570116063/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1334132019/2500000000 : ℝ)*X 2 0+(321264527/625000000 : ℝ)*X 2 1+(-1503710877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((101964861/250000000 : ℝ)*X 0 0+(903514517/2500000000 : ℝ)*X 0 1+(2288607641/5000000000 : ℝ)*X 0 2+(101964861/250000000 : ℝ)*X 1 0+(903514517/2500000000 : ℝ)*X 1 1+(2288607641/5000000000 : ℝ)*X 1 2+(101964861/250000000 : ℝ)*X 2 0+(903514517/2500000000 : ℝ)*X 2 1+(2288607641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-334937687/2500000000 : ℝ)*X 0 0+(1285953089/2500000000 : ℝ)*X 0 1+(1090716599/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251697901/10000000000 : ℝ)*X 1 0+(-148795013/1250000000 : ℝ)*X 1 1+(5453583017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525169783/1000000000 : ℝ)*X 2 0+(2726791541/5000000000 : ℝ)*X 2 1+(-1190360111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((50987769/125000000 : ℝ)*X 0 0+(182653473/400000000 : ℝ)*X 0 1+(362509857/1000000000 : ℝ)*X 0 2+(50987769/125000000 : ℝ)*X 1 0+(182653473/400000000 : ℝ)*X 1 1+(362509857/1000000000 : ℝ)*X 1 2+(50987769/125000000 : ℝ)*X 2 0+(182653473/400000000 : ℝ)*X 2 1+(362509857/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1731_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17689952989914010186701809/2070312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1234495467/100000000000000 : ℝ)*(base19) + (248476817/25000000000000 : ℝ)*(base23) + (8042649/25000000000000 : ℝ)*(lower2) + (204814031/100000000000000 : ℝ)*(upper3) + (27857039/20000000000000 : ℝ)*(upper5) + (131031714700889/6250000000000 : ℝ)*(major0) + (131031714700889/6250000000000 : ℝ)*(major1) + (131031714700889/6250000000000 : ℝ)*(major2) + (394343090396539/12500000000000 : ℝ)*(sp0) + (98586037145797/3125000000000 : ℝ)*(sp1) + (3154753429253703/100000000000000 : ℝ)*(sp2) + (207651187127421/20000000000000 : ℝ)*(sp3) + (9699988659/100000000000000 : ℝ)*(sp4) + (4226810997/100000000000000 : ℝ)*(sp7) + (519130081224051/50000000000000 : ℝ)*(f.failure) + (315475442316097/10000000000000 : ℝ)*(f.sum) + (51248178918127/8943750000000000000000000000 : ℝ)*base65 + (1155268157433904771/223593750000000000000000000000000 : ℝ)*base68 + (505021016891404771/223593750000000000000000000000000 : ℝ)*base70 + (1498148561977186021/223593750000000000000000000000000 : ℝ)*base72 + (138516624786433/35775000000000000000000000000 : ℝ)*base73 + (625903471655311021/223593750000000000000000000000000 : ℝ)*base76 + (642856945434061021/223593750000000000000000000000000 : ℝ)*base78 + (1119191297822029771/223593750000000000000000000000000 : ℝ)*base80 + (172302599181433/35775000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4584979/2500000000000000000000 : ℝ)*base89 + (4584979/2500000000000000000000 : ℝ)*base91 + (4584979/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (432840241521772519381354087/49687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122403657/10000000000000 : ℝ)*(base19) + (311242131/25000000000000 : ℝ)*(base23) + (32106323/100000000000000 : ℝ)*(upper2) + (193467169/100000000000000 : ℝ)*(upper3) + (207803833/100000000000000 : ℝ)*(upper5) + (536328116097549/25000000000000 : ℝ)*(major0) + (536328116097549/25000000000000 : ℝ)*(major1) + (536328116097549/25000000000000 : ℝ)*(major2) + (2953022753/25000000000000 : ℝ)*(sp1) + (375784357/3125000000000 : ℝ)*(sp2) + (1614097301700949/50000000000000 : ℝ)*(sp4) + (3228181567274317/100000000000000 : ℝ)*(sp5) + (50440333333343/1562500000000 : ℝ)*(sp6) + (1062430035003479/100000000000000 : ℝ)*(sp7) + (1062430035003479/100000000000000 : ℝ)*(f.failure) + (1614097301700949/50000000000000 : ℝ)*(f.sum) + (2041267219309/745312500000000000000000000 : ℝ)*base65 + (3406976835609183413/298125000000000000000000000000000 : ℝ)*base67 + (2368850826903558413/298125000000000000000000000000000 : ℝ)*base69 + (95491781679566587/298125000000000000000000000000000 : ℝ)*base72 + (46584473818669/11925000000000000000000000000 : ℝ)*base73 + (1413002037211683413/298125000000000000000000000000000 : ℝ)*base75 + (59130129813941587/298125000000000000000000000000000 : ℝ)*base78 + (1026011199054183413/298125000000000000000000000000000 : ℝ)*base79 + (5811374692997/5962500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (36361609/5000000000000000000000 : ℝ)*base90 + (36361609/5000000000000000000000 : ℝ)*base92 + (36361609/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1731_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2539/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16947/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1731_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1731_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2539/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16947/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1731_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1731_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1731_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5463/1024 : ℝ) ≤ p) (hpb : p ≤ (5471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100962529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2539/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16947/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1731_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
