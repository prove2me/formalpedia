-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1657_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:13.485231+00:00
-- url     : https://prove2.me/submissions/05632c06-e3ef-4270-8591-e8a7f03bebad

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
theorem support_rectangle_w1657_s3_0 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1592733631/10000000000 : ℝ)*x 0 + (5445526411/10000000000 : ℝ)*x 1 + (5184297223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1592733631/10000000000 : ℝ)^4947 ≤ (2465033317187/25000000000000 : ℝ)^3923 := by
    have hnat : (1592733631 : ℕ)^4947*25000000000000^3923 ≤ 2465033317187^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592733631 10000000000 2465033317187 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445526411/10000000000 : ℝ)^4947 ≤ (46466477155069/100000000000000 : ℝ)^3923 := by
    have hnat : (5445526411 : ℕ)^4947*100000000000000^3923 ≤ 46466477155069^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445526411 10000000000 46466477155069 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184297223/10000000000 : ℝ)^4947 ≤ (10918347392481/25000000000000 : ℝ)^3923 := by
    have hnat : (5184297223 : ℕ)^4947*25000000000000^3923 ≤ 10918347392481^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184297223 10000000000 10918347392481 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1592733631/10000000000 : ℝ), (5445526411/10000000000 : ℝ), (5184297223/10000000000 : ℝ)] ![(2465033317187/25000000000000 : ℝ), (46466477155069/100000000000000 : ℝ), (10918347392481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1592733631/10000000000 : ℝ)|^4947 ≤ (2465033317187/25000000000000 : ℝ)^3923
        have hw : |(-1592733631/10000000000 : ℝ)|=(1592733631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445526411/10000000000 : ℝ)|^4947 ≤ (46466477155069/100000000000000 : ℝ)^3923
        have hw : |(5445526411/10000000000 : ℝ)|=(5445526411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184297223/10000000000 : ℝ)|^4947 ≤ (10918347392481/25000000000000 : ℝ)^3923
        have hw : |(5184297223/10000000000 : ℝ)|=(5184297223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s3_1 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83542183/156250000 : ℝ)*x 0 + (-1727176253/10000000000 : ℝ)*x 1 + (129607429/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83542183/156250000 : ℝ)^4947 ≤ (5675700564761/12500000000000 : ℝ)^3923 := by
    have hnat : (83542183 : ℕ)^4947*12500000000000^3923 ≤ 5675700564761^3923*156250000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83542183 156250000 5675700564761 12500000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1727176253/10000000000 : ℝ)^4947 ≤ (1092100657179/10000000000000 : ℝ)^3923 := by
    have hnat : (1727176253 : ℕ)^4947*10000000000000^3923 ≤ 1092100657179^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727176253 10000000000 1092100657179 10000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129607429/250000000 : ℝ)^4947 ≤ (4367338890067/10000000000000 : ℝ)^3923 := by
    have hnat : (129607429 : ℕ)^4947*10000000000000^3923 ≤ 4367338890067^3923*250000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129607429 250000000 4367338890067 10000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83542183/156250000 : ℝ), (-1727176253/10000000000 : ℝ), (129607429/250000000 : ℝ)] ![(5675700564761/12500000000000 : ℝ), (1092100657179/10000000000000 : ℝ), (4367338890067/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83542183/156250000 : ℝ)|^4947 ≤ (5675700564761/12500000000000 : ℝ)^3923
        have hw : |(83542183/156250000 : ℝ)|=(83542183/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1727176253/10000000000 : ℝ)|^4947 ≤ (1092100657179/10000000000000 : ℝ)^3923
        have hw : |(-1727176253/10000000000 : ℝ)|=(1727176253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129607429/250000000 : ℝ)|^4947 ≤ (4367338890067/10000000000000 : ℝ)^3923
        have hw : |(129607429/250000000 : ℝ)|=(129607429/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s3_2 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42773599/80000000 : ℝ)*x 0 + (5184296969/10000000000 : ℝ)*x 1 + (-53974259/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42773599/80000000 : ℝ)^4947 ≤ (1418925195739/3125000000000 : ℝ)^3923 := by
    have hnat : (42773599 : ℕ)^4947*3125000000000^3923 ≤ 1418925195739^3923*80000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42773599 80000000 1418925195739 3125000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184296969/10000000000 : ℝ)^4947 ≤ (43673386871661/100000000000000 : ℝ)^3923 := by
    have hnat : (5184296969 : ℕ)^4947*100000000000000^3923 ≤ 43673386871661^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184296969 10000000000 43673386871661 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53974259/312500000 : ℝ)^4947 ≤ (10921006850863/100000000000000 : ℝ)^3923 := by
    have hnat : (53974259 : ℕ)^4947*100000000000000^3923 ≤ 10921006850863^3923*312500000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53974259 312500000 10921006850863 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42773599/80000000 : ℝ), (5184296969/10000000000 : ℝ), (-53974259/312500000 : ℝ)] ![(1418925195739/3125000000000 : ℝ), (43673386871661/100000000000000 : ℝ), (10921006850863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42773599/80000000 : ℝ)|^4947 ≤ (1418925195739/3125000000000 : ℝ)^3923
        have hw : |(42773599/80000000 : ℝ)|=(42773599/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184296969/10000000000 : ℝ)|^4947 ≤ (43673386871661/100000000000000 : ℝ)^3923
        have hw : |(5184296969/10000000000 : ℝ)|=(5184296969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53974259/312500000 : ℝ)|^4947 ≤ (10921006850863/100000000000000 : ℝ)^3923
        have hw : |(-53974259/312500000 : ℝ)|=(53974259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s3_3 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (260961639/625000000 : ℝ)*x 0 + (3844463141/10000000000 : ℝ)*x 1 + (1131573059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260961639/625000000 : ℝ)^4947 ≤ (33242149785271/100000000000000 : ℝ)^3923 := by
    have hnat : (260961639 : ℕ)^4947*100000000000000^3923 ≤ 33242149785271^3923*625000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260961639 625000000 33242149785271 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3844463141/10000000000 : ℝ)^4947 ≤ (14977438966629/50000000000000 : ℝ)^3923 := by
    have hnat : (3844463141 : ℕ)^4947*50000000000000^3923 ≤ 14977438966629^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3844463141 10000000000 14977438966629 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131573059/2500000000 : ℝ)^4947 ≤ (36802972261323/100000000000000 : ℝ)^3923 := by
    have hnat : (1131573059 : ℕ)^4947*100000000000000^3923 ≤ 36802972261323^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131573059 2500000000 36802972261323 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260961639/625000000 : ℝ), (3844463141/10000000000 : ℝ), (1131573059/2500000000 : ℝ)] ![(33242149785271/100000000000000 : ℝ), (14977438966629/50000000000000 : ℝ), (36802972261323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260961639/625000000 : ℝ)|^4947 ≤ (33242149785271/100000000000000 : ℝ)^3923
        have hw : |(260961639/625000000 : ℝ)|=(260961639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3844463141/10000000000 : ℝ)|^4947 ≤ (14977438966629/50000000000000 : ℝ)^3923
        have hw : |(3844463141/10000000000 : ℝ)|=(3844463141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131573059/2500000000 : ℝ)|^4947 ≤ (36802972261323/100000000000000 : ℝ)^3923
        have hw : |(1131573059/2500000000 : ℝ)|=(1131573059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s3_4 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-199099653/1250000000 : ℝ)*x 0 + (2593140361/5000000000 : ℝ)*x 1 + (544352187/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199099653/1250000000 : ℝ)^4947 ≤ (4930314858973/50000000000000 : ℝ)^3923 := by
    have hnat : (199099653 : ℕ)^4947*50000000000000^3923 ≤ 4930314858973^3923*1250000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199099653 1250000000 4930314858973 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593140361/5000000000 : ℝ)^4947 ≤ (4369446149817/10000000000000 : ℝ)^3923 := by
    have hnat : (2593140361 : ℕ)^4947*10000000000000^3923 ≤ 4369446149817^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593140361 5000000000 4369446149817 10000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544352187/1000000000 : ℝ)^4947 ≤ (23222454386757/50000000000000 : ℝ)^3923 := by
    have hnat : (544352187 : ℕ)^4947*50000000000000^3923 ≤ 23222454386757^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544352187 1000000000 23222454386757 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199099653/1250000000 : ℝ), (2593140361/5000000000 : ℝ), (544352187/1000000000 : ℝ)] ![(4930314858973/50000000000000 : ℝ), (4369446149817/10000000000000 : ℝ), (23222454386757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199099653/1250000000 : ℝ)|^4947 ≤ (4930314858973/50000000000000 : ℝ)^3923
        have hw : |(-199099653/1250000000 : ℝ)|=(199099653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593140361/5000000000 : ℝ)|^4947 ≤ (4369446149817/10000000000000 : ℝ)^3923
        have hw : |(2593140361/5000000000 : ℝ)|=(2593140361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544352187/1000000000 : ℝ)|^4947 ≤ (23222454386757/50000000000000 : ℝ)^3923
        have hw : |(544352187/1000000000 : ℝ)|=(544352187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s3_5 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276855467/10000000000 : ℝ)*x 0 + (-3669879/25000000 : ℝ)*x 1 + (170110059/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276855467/10000000000 : ℝ)^4947 ≤ (1116473116279/2500000000000 : ℝ)^3923 := by
    have hnat : (5276855467 : ℕ)^4947*2500000000000^3923 ≤ 1116473116279^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276855467 10000000000 1116473116279 2500000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3669879/25000000 : ℝ)^4947 ≤ (278005198967/3125000000000 : ℝ)^3923 := by
    have hnat : (3669879 : ℕ)^4947*3125000000000^3923 ≤ 278005198967^3923*25000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3669879 25000000 278005198967 3125000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170110059/312500000 : ℝ)^4947 ≤ (2322245448359/5000000000000 : ℝ)^3923 := by
    have hnat : (170110059 : ℕ)^4947*5000000000000^3923 ≤ 2322245448359^3923*312500000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170110059 312500000 2322245448359 5000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276855467/10000000000 : ℝ), (-3669879/25000000 : ℝ), (170110059/312500000 : ℝ)] ![(1116473116279/2500000000000 : ℝ), (278005198967/3125000000000 : ℝ), (2322245448359/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276855467/10000000000 : ℝ)|^4947 ≤ (1116473116279/2500000000000 : ℝ)^3923
        have hw : |(5276855467/10000000000 : ℝ)|=(5276855467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3669879/25000000 : ℝ)|^4947 ≤ (278005198967/3125000000000 : ℝ)^3923
        have hw : |(-3669879/25000000 : ℝ)|=(3669879/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170110059/312500000 : ℝ)|^4947 ≤ (2322245448359/5000000000000 : ℝ)^3923
        have hw : |(170110059/312500000 : ℝ)|=(170110059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s3_6 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276855941/10000000000 : ℝ)*x 0 + (5443521507/10000000000 : ℝ)*x 1 + (-58718059/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276855941/10000000000 : ℝ)^4947 ≤ (22329464854907/50000000000000 : ℝ)^3923 := by
    have hnat : (5276855941 : ℕ)^4947*50000000000000^3923 ≤ 22329464854907^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276855941 10000000000 22329464854907 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443521507/10000000000 : ℝ)^4947 ≤ (11611226216977/25000000000000 : ℝ)^3923 := by
    have hnat : (5443521507 : ℕ)^4947*25000000000000^3923 ≤ 11611226216977^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443521507 10000000000 11611226216977 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58718059/400000000 : ℝ)^4947 ≤ (8896165411677/100000000000000 : ℝ)^3923 := by
    have hnat : (58718059 : ℕ)^4947*100000000000000^3923 ≤ 8896165411677^3923*400000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58718059 400000000 8896165411677 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276855941/10000000000 : ℝ), (5443521507/10000000000 : ℝ), (-58718059/400000000 : ℝ)] ![(22329464854907/50000000000000 : ℝ), (11611226216977/25000000000000 : ℝ), (8896165411677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276855941/10000000000 : ℝ)|^4947 ≤ (22329464854907/50000000000000 : ℝ)^3923
        have hw : |(5276855941/10000000000 : ℝ)|=(5276855941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443521507/10000000000 : ℝ)|^4947 ≤ (11611226216977/25000000000000 : ℝ)^3923
        have hw : |(5443521507/10000000000 : ℝ)|=(5443521507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58718059/400000000 : ℝ)|^4947 ≤ (8896165411677/100000000000000 : ℝ)^3923
        have hw : |(-58718059/400000000 : ℝ)|=(58718059/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s3_7 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (417555207/1000000000 : ℝ)*x 0 + (1130278613/2500000000 : ℝ)*x 1 + (1924847581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417555207/1000000000 : ℝ)^4947 ≤ (1329752592801/4000000000000 : ℝ)^3923 := by
    have hnat : (417555207 : ℕ)^4947*4000000000000^3923 ≤ 1329752592801^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417555207 1000000000 1329752592801 4000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130278613/2500000000 : ℝ)^4947 ≤ (36749890787449/100000000000000 : ℝ)^3923 := by
    have hnat : (1130278613 : ℕ)^4947*100000000000000^3923 ≤ 36749890787449^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130278613 2500000000 36749890787449 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924847581/5000000000 : ℝ)^4947 ≤ (30006294377469/100000000000000 : ℝ)^3923 := by
    have hnat : (1924847581 : ℕ)^4947*100000000000000^3923 ≤ 30006294377469^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924847581 5000000000 30006294377469 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417555207/1000000000 : ℝ), (1130278613/2500000000 : ℝ), (1924847581/5000000000 : ℝ)] ![(1329752592801/4000000000000 : ℝ), (36749890787449/100000000000000 : ℝ), (30006294377469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417555207/1000000000 : ℝ)|^4947 ≤ (1329752592801/4000000000000 : ℝ)^3923
        have hw : |(417555207/1000000000 : ℝ)|=(417555207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130278613/2500000000 : ℝ)|^4947 ≤ (36749890787449/100000000000000 : ℝ)^3923
        have hw : |(1130278613/2500000000 : ℝ)|=(1130278613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1924847581/5000000000 : ℝ)|^4947 ≤ (30006294377469/100000000000000 : ℝ)^3923
        have hw : |(1924847581/5000000000 : ℝ)|=(1924847581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1657_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10703/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8129/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16323/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16323/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16323/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16323/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16323/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16323/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2661/25000 : ℝ) ^ (4943/1024 : ℝ) ≤ (201229094748849/10000000000000000000 : ℝ) := by
    have hpowers : (2661/25000 : ℝ)^4943 ≤ (201229094748849/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2661 : ℕ)^4943*10000000000000000000^1024 ≤ 201229094748849^1024*25000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2661 25000 201229094748849 10000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2661/25000 : ℝ)) (X := (201229094748849/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16323/100000 : ℝ) ^ (4943/1024 : ℝ) ≤ (3962859409697127/25000000000000000000 : ℝ) := by
    have hpowers : (16323/100000 : ℝ)^4943 ≤ (3962859409697127/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16323 : ℕ)^4943*25000000000000000000^1024 ≤ 3962859409697127^1024*100000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16323 100000 3962859409697127 25000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16323/100000 : ℝ)) (X := (3962859409697127/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000201229094748849/5000000000000000000 : ℝ) ≤ (10000083372569533/10000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (5000201229094748849/5000000000000000000 : ℝ)^1024 ≤ (10000083372569533/10000000000000000 : ℝ)^4943 := by
      have hnat : (5000201229094748849 : ℕ)^1024*10000000000000000^4943 ≤ 10000083372569533^4943*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000201229094748849 5000000000000000000 10000083372569533 10000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083372569533/10000000000000000 : ℝ)) (X := (5000201229094748849/5000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008931864293138499/50000000000000000000 : ℝ) ≤ (5000185020866131/5000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (50008931864293138499/50000000000000000000 : ℝ)^1024 ≤ (5000185020866131/5000000000000000 : ℝ)^4943 := by
      have hnat : (50008931864293138499 : ℕ)^1024*5000000000000000^4943 ≤ 5000185020866131^4943*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008931864293138499 50000000000000000000 5000185020866131 5000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000185020866131/5000000000000000 : ℝ)) (X := (50008931864293138499/50000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503962859409697127/12500000000000000000 : ℝ) ≤ (10000656710894991/10000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (12503962859409697127/12500000000000000000 : ℝ)^1024 ≤ (10000656710894991/10000000000000000 : ℝ)^4943 := by
      have hnat : (12503962859409697127 : ℕ)^1024*10000000000000000^4943 ≤ 10000656710894991^4943*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503962859409697127 12500000000000000000 10000656710894991 10000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000656710894991/10000000000000000 : ℝ)) (X := (12503962859409697127/12500000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(201229094748849/10000000000000000000 : ℝ) ≤ ((3785624723979080197/3786000000000000000 : ℝ)+2*(286669162729/567900000000000 : ℝ)*(2661/25000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (3785624723979080197/3786000000000000000 : ℝ)+2*(286669162729/567900000000000 : ℝ)*(2661/25000 : ℝ)=(10000083372569533/10000000000000000 : ℝ) by norm_num, show 1+2*(201229094748849/10000000000000000000 : ℝ)=(5000201229094748849/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3962859409697127/25000000000000000000 : ℝ)+(201229094748849/10000000000000000000 : ℝ) ≤ ((3785624723979080197/3786000000000000000 : ℝ)+(286669162729/567900000000000 : ℝ)*((16323/100000 : ℝ)+(2661/25000 : ℝ)))^(4943/1024 : ℝ) := by
    rw [show (3785624723979080197/3786000000000000000 : ℝ)+(286669162729/567900000000000 : ℝ)*((16323/100000 : ℝ)+(2661/25000 : ℝ))=(5000185020866131/5000000000000000 : ℝ) by norm_num, show 1+(3962859409697127/25000000000000000000 : ℝ)+(201229094748849/10000000000000000000 : ℝ)=(50008931864293138499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3962859409697127/25000000000000000000 : ℝ) ≤ ((3785624723979080197/3786000000000000000 : ℝ)+2*(286669162729/567900000000000 : ℝ)*(16323/100000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (3785624723979080197/3786000000000000000 : ℝ)+2*(286669162729/567900000000000 : ℝ)*(16323/100000 : ℝ)=(10000656710894991/10000000000000000 : ℝ) by norm_num, show 1+2*(3962859409697127/25000000000000000000 : ℝ)=(12503962859409697127/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3785624723979080197/3786000000000000000 : ℝ)*(X 1 0+X 2 0)+(286669162729/567900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16323/100000 : ℝ)) (c := (3785624723979080197/3786000000000000000 : ℝ)) (alpha := (286669162729/567900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3785624723979080197/3786000000000000000 : ℝ)*(X 0 1+X 2 1)+(286669162729/567900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16323/100000 : ℝ)) (c := (3785624723979080197/3786000000000000000 : ℝ)) (alpha := (286669162729/567900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3785624723979080197/3786000000000000000 : ℝ)*(X 0 2+X 1 2)+(286669162729/567900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16323/100000 : ℝ)) (c := (3785624723979080197/3786000000000000000 : ℝ)) (alpha := (286669162729/567900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1592733631/10000000000 : ℝ)*X 0 0+(5445526411/10000000000 : ℝ)*X 0 1+(5184297223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83542183/156250000 : ℝ)*X 1 0+(-1727176253/10000000000 : ℝ)*X 1 1+(129607429/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42773599/80000000 : ℝ)*X 2 0+(5184296969/10000000000 : ℝ)*X 2 1+(-53974259/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((260961639/625000000 : ℝ)*X 0 0+(3844463141/10000000000 : ℝ)*X 0 1+(1131573059/2500000000 : ℝ)*X 0 2+(260961639/625000000 : ℝ)*X 1 0+(3844463141/10000000000 : ℝ)*X 1 1+(1131573059/2500000000 : ℝ)*X 1 2+(260961639/625000000 : ℝ)*X 2 0+(3844463141/10000000000 : ℝ)*X 2 1+(1131573059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-199099653/1250000000 : ℝ)*X 0 0+(2593140361/5000000000 : ℝ)*X 0 1+(544352187/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276855467/10000000000 : ℝ)*X 1 0+(-3669879/25000000 : ℝ)*X 1 1+(170110059/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276855941/10000000000 : ℝ)*X 2 0+(5443521507/10000000000 : ℝ)*X 2 1+(-58718059/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((417555207/1000000000 : ℝ)*X 0 0+(1130278613/2500000000 : ℝ)*X 0 1+(1924847581/5000000000 : ℝ)*X 0 2+(417555207/1000000000 : ℝ)*X 1 0+(1130278613/2500000000 : ℝ)*X 1 1+(1924847581/5000000000 : ℝ)*X 1 2+(417555207/1000000000 : ℝ)*X 2 0+(1130278613/2500000000 : ℝ)*X 2 1+(1924847581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63977284288271924108519359/23662500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21681699/6250000000000 : ℝ)*(base19) + (456130693/100000000000000 : ℝ)*(base23) + (1794187/4000000000000 : ℝ)*(lower2) + (40855723/100000000000000 : ℝ)*(lower4) + (1022947/6250000000000 : ℝ)*(lower5) + (661839289800551/25000000000000 : ℝ)*(major0) + (661839289800551/25000000000000 : ℝ)*(major1) + (661839289800551/25000000000000 : ℝ)*(major2) + (382806142242779/10000000000000 : ℝ)*(sp0) + (3828066589786747/100000000000000 : ℝ)*(sp1) + (1914033240281619/50000000000000 : ℝ)*(sp2) + (1466645064467957/100000000000000 : ℝ)*(sp3) + (275713307/5000000000000 : ℝ)*(sp4) + (556779449/25000000000000 : ℝ)*(sp7) + (1466647291585753/100000000000000 : ℝ)*(f.failure) + (382806693669393/10000000000000 : ℝ)*(f.sum) + (40744199699147/14197500000000000000000000000 : ℝ)*base66 + (2862676064023895641/283950000000000000000000000000000 : ℝ)*base67 + (2243120369837645641/283950000000000000000000000000000 : ℝ)*base69 + (2943203303544545641/283950000000000000000000000000000 : ℝ)*base71 + (8570968097897/14197500000000000000000000000 : ℝ)*base74 + (604095789115145641/283950000000000000000000000000000 : ℝ)*base75 + (526063264160154359/283950000000000000000000000000000 : ℝ)*base78 + (1121633557598495641/283950000000000000000000000000000 : ℝ)*base79 + (1350114618251/1774687500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16216223/10000000000000000000000 : ℝ)*base90 + (16216223/10000000000000000000000 : ℝ)*base92 + (16216223/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13817305711206025386581/2366250000000000000000000000 : ℝ) := by norm_num
    linear_combination (967642599/100000000000000 : ℝ)*(base19) + (754592787/50000000000000 : ℝ)*(base23) + (69274849/100000000000000 : ℝ)*(upper3) + (1661679/2000000000000 : ℝ)*(lower4) + (1299071/781250000000 : ℝ)*(upper5) + (1344196870745953/50000000000000 : ℝ)*(major0) + (1344196870745953/50000000000000 : ℝ)*(major1) + (1344196870745953/50000000000000 : ℝ)*(major2) + (14606118673/100000000000000 : ℝ)*(sp1) + (17243134087/100000000000000 : ℝ)*(sp2) + (77748111061217/2000000000000 : ℝ)*(sp4) + (3887389979299577/100000000000000 : ℝ)*(sp5) + (971846700185297/25000000000000 : ℝ)*(sp6) + (1489381735278747/100000000000000 : ℝ)*(sp7) + (1489381735278747/100000000000000 : ℝ)*(f.failure) + (77748111061217/2000000000000 : ℝ)*(f.sum) + (11930528493731/7098750000000000000000000000 : ℝ)*base65 + (3412083582542281777/567900000000000000000000000000000 : ℝ)*base68 + (6913372314485281777/567900000000000000000000000000000 : ℝ)*base70 + (1377655989492181777/567900000000000000000000000000000 : ℝ)*base72 + (20097363967651/28395000000000000000000000000 : ℝ)*base74 + (497881381762318223/567900000000000000000000000000000 : ℝ)*base75 + (563325466183618223/567900000000000000000000000000000 : ℝ)*base77 + (2684050939357618223/567900000000000000000000000000000 : ℝ)*base79 + (28381602903109/7098750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (34003277/10000000000000000000000 : ℝ)*base90 + (34003277/10000000000000000000000 : ℝ)*base92 + (34003277/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1657_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8129/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1657_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1657_s4_0 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99548237/625000000 : ℝ)*x 0 + (2722665531/5000000000 : ℝ)*x 1 + (5184467049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99548237/625000000 : ℝ)^4947 ≤ (9860431178241/100000000000000 : ℝ)^3923 := by
    have hnat : (99548237 : ℕ)^4947*100000000000000^3923 ≤ 9860431178241^3923*625000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99548237 625000000 9860431178241 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722665531/5000000000 : ℝ)^4947 ≤ (23232187577707/50000000000000 : ℝ)^3923 := by
    have hnat : (2722665531 : ℕ)^4947*50000000000000^3923 ≤ 23232187577707^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722665531 5000000000 23232187577707 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184467049/10000000000 : ℝ)^4947 ≤ (10918798413369/25000000000000 : ℝ)^3923 := by
    have hnat : (5184467049 : ℕ)^4947*25000000000000^3923 ≤ 10918798413369^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184467049 10000000000 10918798413369 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99548237/625000000 : ℝ), (2722665531/5000000000 : ℝ), (5184467049/10000000000 : ℝ)] ![(9860431178241/100000000000000 : ℝ), (23232187577707/50000000000000 : ℝ), (10918798413369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99548237/625000000 : ℝ)|^4947 ≤ (9860431178241/100000000000000 : ℝ)^3923
        have hw : |(-99548237/625000000 : ℝ)|=(99548237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722665531/5000000000 : ℝ)|^4947 ≤ (23232187577707/50000000000000 : ℝ)^3923
        have hw : |(2722665531/5000000000 : ℝ)|=(2722665531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184467049/10000000000 : ℝ)|^4947 ≤ (10918798413369/25000000000000 : ℝ)^3923
        have hw : |(5184467049/10000000000 : ℝ)|=(5184467049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s4_1 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213865871/400000000 : ℝ)*x 0 + (-345404201/2000000000 : ℝ)*x 1 + (103689341/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213865871/400000000 : ℝ)^4947 ≤ (22702518809319/50000000000000 : ℝ)^3923 := by
    have hnat : (213865871 : ℕ)^4947*50000000000000^3923 ≤ 22702518809319^3923*400000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213865871 400000000 22702518809319 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345404201/2000000000 : ℝ)^4947 ≤ (5459884357317/50000000000000 : ℝ)^3923 := by
    have hnat : (345404201 : ℕ)^4947*50000000000000^3923 ≤ 5459884357317^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345404201 2000000000 5459884357317 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103689341/200000000 : ℝ)^4947 ≤ (43675193664099/100000000000000 : ℝ)^3923 := by
    have hnat : (103689341 : ℕ)^4947*100000000000000^3923 ≤ 43675193664099^3923*200000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103689341 200000000 43675193664099 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213865871/400000000 : ℝ), (-345404201/2000000000 : ℝ), (103689341/200000000 : ℝ)] ![(22702518809319/50000000000000 : ℝ), (5459884357317/50000000000000 : ℝ), (43675193664099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213865871/400000000 : ℝ)|^4947 ≤ (22702518809319/50000000000000 : ℝ)^3923
        have hw : |(213865871/400000000 : ℝ)|=(213865871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-345404201/2000000000 : ℝ)|^4947 ≤ (5459884357317/50000000000000 : ℝ)^3923
        have hw : |(-345404201/2000000000 : ℝ)|=(345404201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103689341/200000000 : ℝ)|^4947 ≤ (43675193664099/100000000000000 : ℝ)^3923
        have hw : |(103689341/200000000 : ℝ)|=(103689341/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s4_2 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346646749/10000000000 : ℝ)*x 0 + (1296116769/2500000000 : ℝ)*x 1 + (-1727021003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346646749/10000000000 : ℝ)^4947 ≤ (22702518670103/50000000000000 : ℝ)^3923 := by
    have hnat : (5346646749 : ℕ)^4947*50000000000000^3923 ≤ 22702518670103^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346646749 10000000000 22702518670103 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296116769/2500000000 : ℝ)^4947 ≤ (43675193940301/100000000000000 : ℝ)^3923 := by
    have hnat : (1296116769 : ℕ)^4947*100000000000000^3923 ≤ 43675193940301^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296116769 2500000000 43675193940301 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1727021003/10000000000 : ℝ)^4947 ≤ (170621385917/1562500000000 : ℝ)^3923 := by
    have hnat : (1727021003 : ℕ)^4947*1562500000000^3923 ≤ 170621385917^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727021003 10000000000 170621385917 1562500000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346646749/10000000000 : ℝ), (1296116769/2500000000 : ℝ), (-1727021003/10000000000 : ℝ)] ![(22702518670103/50000000000000 : ℝ), (43675193940301/100000000000000 : ℝ), (170621385917/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346646749/10000000000 : ℝ)|^4947 ≤ (22702518670103/50000000000000 : ℝ)^3923
        have hw : |(5346646749/10000000000 : ℝ)|=(5346646749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296116769/2500000000 : ℝ)|^4947 ≤ (43675193940301/100000000000000 : ℝ)^3923
        have hw : |(1296116769/2500000000 : ℝ)|=(1296116769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1727021003/10000000000 : ℝ)|^4947 ≤ (170621385917/1562500000000 : ℝ)^3923
        have hw : |(-1727021003/10000000000 : ℝ)|=(1727021003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s4_3 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4175411747/10000000000 : ℝ)*x 0 + (38449371/100000000 : ℝ)*x 1 + (4525813047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175411747/10000000000 : ℝ)^4947 ≤ (16621203012987/50000000000000 : ℝ)^3923 := by
    have hnat : (4175411747 : ℕ)^4947*50000000000000^3923 ≤ 16621203012987^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175411747 10000000000 16621203012987 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38449371/100000000 : ℝ)^4947 ≤ (5991906980173/20000000000000 : ℝ)^3923 := by
    have hnat : (38449371 : ℕ)^4947*20000000000000^3923 ≤ 5991906980173^3923*100000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38449371 100000000 5991906980173 20000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525813047/10000000000 : ℝ)^4947 ≤ (2299878691119/6250000000000 : ℝ)^3923 := by
    have hnat : (4525813047 : ℕ)^4947*6250000000000^3923 ≤ 2299878691119^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525813047 10000000000 2299878691119 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175411747/10000000000 : ℝ), (38449371/100000000 : ℝ), (4525813047/10000000000 : ℝ)] ![(16621203012987/50000000000000 : ℝ), (5991906980173/20000000000000 : ℝ), (2299878691119/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175411747/10000000000 : ℝ)|^4947 ≤ (16621203012987/50000000000000 : ℝ)^3923
        have hw : |(4175411747/10000000000 : ℝ)|=(4175411747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38449371/100000000 : ℝ)|^4947 ≤ (5991906980173/20000000000000 : ℝ)^3923
        have hw : |(38449371/100000000 : ℝ)|=(38449371/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525813047/10000000000 : ℝ)|^4947 ≤ (2299878691119/6250000000000 : ℝ)^3923
        have hw : |(4525813047/10000000000 : ℝ)|=(4525813047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s4_4 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99552183/625000000 : ℝ)*x 0 + (324152823/625000000 : ℝ)*x 1 + (544333213/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99552183/625000000 : ℝ)^4947 ≤ (9860924062857/100000000000000 : ℝ)^3923 := by
    have hnat : (99552183 : ℕ)^4947*100000000000000^3923 ≤ 9860924062857^3923*625000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99552183 625000000 9860924062857 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324152823/625000000 : ℝ)^4947 ≤ (43696208603483/100000000000000 : ℝ)^3923 := by
    have hnat : (324152823 : ℕ)^4947*100000000000000^3923 ≤ 43696208603483^3923*625000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324152823 625000000 43696208603483 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544333213/1000000000 : ℝ)^4947 ≤ (23221433661951/50000000000000 : ℝ)^3923 := by
    have hnat : (544333213 : ℕ)^4947*50000000000000^3923 ≤ 23221433661951^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544333213 1000000000 23221433661951 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99552183/625000000 : ℝ), (324152823/625000000 : ℝ), (544333213/1000000000 : ℝ)] ![(9860924062857/100000000000000 : ℝ), (43696208603483/100000000000000 : ℝ), (23221433661951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99552183/625000000 : ℝ)|^4947 ≤ (9860924062857/100000000000000 : ℝ)^3923
        have hw : |(-99552183/625000000 : ℝ)|=(99552183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324152823/625000000 : ℝ)|^4947 ≤ (43696208603483/100000000000000 : ℝ)^3923
        have hw : |(324152823/625000000 : ℝ)|=(324152823/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544333213/1000000000 : ℝ)|^4947 ≤ (23221433661951/50000000000000 : ℝ)^3923
        have hw : |(544333213/1000000000 : ℝ)|=(544333213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s4_5 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276900369/10000000000 : ℝ)*x 0 + (-73407797/500000000 : ℝ)*x 1 + (1088666441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276900369/10000000000 : ℝ)^4947 ≤ (22329701928903/50000000000000 : ℝ)^3923 := by
    have hnat : (5276900369 : ℕ)^4947*50000000000000^3923 ≤ 22329701928903^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276900369 10000000000 22329701928903 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73407797/500000000 : ℝ)^4947 ≤ (4448863994691/50000000000000 : ℝ)^3923 := by
    have hnat : (73407797 : ℕ)^4947*50000000000000^3923 ≤ 4448863994691^3923*500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73407797 500000000 4448863994691 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088666441/2000000000 : ℝ)^4947 ≤ (23221434065419/50000000000000 : ℝ)^3923 := by
    have hnat : (1088666441 : ℕ)^4947*50000000000000^3923 ≤ 23221434065419^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088666441 2000000000 23221434065419 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276900369/10000000000 : ℝ), (-73407797/500000000 : ℝ), (1088666441/2000000000 : ℝ)] ![(22329701928903/50000000000000 : ℝ), (4448863994691/50000000000000 : ℝ), (23221434065419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276900369/10000000000 : ℝ)|^4947 ≤ (22329701928903/50000000000000 : ℝ)^3923
        have hw : |(5276900369/10000000000 : ℝ)|=(5276900369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-73407797/500000000 : ℝ)|^4947 ≤ (4448863994691/50000000000000 : ℝ)^3923
        have hw : |(-73407797/500000000 : ℝ)|=(73407797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088666441/2000000000 : ℝ)|^4947 ≤ (23221434065419/50000000000000 : ℝ)^3923
        have hw : |(1088666441/2000000000 : ℝ)|=(1088666441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s4_6 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659612529/1250000000 : ℝ)*x 0 + (5443332341/10000000000 : ℝ)*x 1 + (-1468155941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659612529/1250000000 : ℝ)^4947 ≤ (22329701197851/50000000000000 : ℝ)^3923 := by
    have hnat : (659612529 : ℕ)^4947*50000000000000^3923 ≤ 22329701197851^3923*1250000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659612529 1250000000 22329701197851 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443332341/10000000000 : ℝ)^4947 ≤ (23221434797041/50000000000000 : ℝ)^3923 := by
    have hnat : (5443332341 : ℕ)^4947*50000000000000^3923 ≤ 23221434797041^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443332341 10000000000 23221434797041 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1468155941/10000000000 : ℝ)^4947 ≤ (278053999907/3125000000000 : ℝ)^3923 := by
    have hnat : (1468155941 : ℕ)^4947*3125000000000^3923 ≤ 278053999907^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468155941 10000000000 278053999907 3125000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659612529/1250000000 : ℝ), (5443332341/10000000000 : ℝ), (-1468155941/10000000000 : ℝ)] ![(22329701197851/50000000000000 : ℝ), (23221434797041/50000000000000 : ℝ), (278053999907/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659612529/1250000000 : ℝ)|^4947 ≤ (22329701197851/50000000000000 : ℝ)^3923
        have hw : |(659612529/1250000000 : ℝ)|=(659612529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443332341/10000000000 : ℝ)|^4947 ≤ (23221434797041/50000000000000 : ℝ)^3923
        have hw : |(5443332341/10000000000 : ℝ)|=(5443332341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1468155941/10000000000 : ℝ)|^4947 ≤ (278053999907/3125000000000 : ℝ)^3923
        have hw : |(-1468155941/10000000000 : ℝ)|=(1468155941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s4_7 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2087788357/5000000000 : ℝ)*x 0 + (904130007/2000000000 : ℝ)*x 1 + (481269287/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087788357/5000000000 : ℝ)^4947 ≤ (16622031119239/50000000000000 : ℝ)^3923 := by
    have hnat : (2087788357 : ℕ)^4947*50000000000000^3923 ≤ 16622031119239^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087788357 5000000000 16622031119239 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904130007/2000000000 : ℝ)^4947 ≤ (146980521857/400000000000 : ℝ)^3923 := by
    have hnat : (904130007 : ℕ)^4947*400000000000^3923 ≤ 146980521857^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904130007 2000000000 146980521857 400000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481269287/1250000000 : ℝ)^4947 ≤ (15005403639413/50000000000000 : ℝ)^3923 := by
    have hnat : (481269287 : ℕ)^4947*50000000000000^3923 ≤ 15005403639413^3923*1250000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481269287 1250000000 15005403639413 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087788357/5000000000 : ℝ), (904130007/2000000000 : ℝ), (481269287/1250000000 : ℝ)] ![(16622031119239/50000000000000 : ℝ), (146980521857/400000000000 : ℝ), (15005403639413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087788357/5000000000 : ℝ)|^4947 ≤ (16622031119239/50000000000000 : ℝ)^3923
        have hw : |(2087788357/5000000000 : ℝ)|=(2087788357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904130007/2000000000 : ℝ)|^4947 ≤ (146980521857/400000000000 : ℝ)^3923
        have hw : |(904130007/2000000000 : ℝ)|=(904130007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481269287/1250000000 : ℝ)|^4947 ≤ (15005403639413/50000000000000 : ℝ)^3923
        have hw : |(481269287/1250000000 : ℝ)|=(481269287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1657_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8129/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5353/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8127/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8129/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10703/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8129/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10703/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8129/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10703/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8129/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10703/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8129/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10703/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8129/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10703/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10703/100000 : ℝ) ^ (4943/1024 : ℝ) ≤ (1033353983056743/50000000000000000000 : ℝ) := by
    have hpowers : (10703/100000 : ℝ)^4943 ≤ (1033353983056743/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10703 : ℕ)^4943*50000000000000000000^1024 ≤ 1033353983056743^1024*100000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10703 100000 1033353983056743 50000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10703/100000 : ℝ)) (X := (1033353983056743/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8129/50000 : ℝ) ^ (4943/1024 : ℝ) ≤ (124392404910479/800000000000000000 : ℝ) := by
    have hpowers : (8129/50000 : ℝ)^4943 ≤ (124392404910479/800000000000000000 : ℝ)^1024 := by
      have hnat : (8129 : ℕ)^4943*800000000000000000^1024 ≤ 124392404910479^1024*50000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8129 50000 124392404910479 800000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8129/50000 : ℝ)) (X := (124392404910479/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001033353983056743/25000000000000000000 : ℝ) ≤ (2000017125424083/2000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (25001033353983056743/25000000000000000000 : ℝ)^1024 ≤ (2000017125424083/2000000000000000 : ℝ)^4943 := by
      have hnat : (25001033353983056743 : ℕ)^1024*2000000000000000^4943 ≤ 2000017125424083^4943*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001033353983056743 25000000000000000000 2000017125424083 2000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000017125424083/2000000000000000 : ℝ)) (X := (25001033353983056743/25000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017615758579923361/100000000000000000000 : ℝ) ≤ (2000072981093453/2000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (100017615758579923361/100000000000000000000 : ℝ)^1024 ≤ (2000072981093453/2000000000000000 : ℝ)^4943 := by
      have hnat : (100017615758579923361 : ℕ)^1024*2000000000000000^4943 ≤ 2000072981093453^4943*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017615758579923361 100000000000000000000 2000072981093453 2000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000072981093453/2000000000000000 : ℝ)) (X := (100017615758579923361/100000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400124392404910479/400000000000000000 : ℝ) ≤ (2000128836762823/2000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (400124392404910479/400000000000000000 : ℝ)^1024 ≤ (2000128836762823/2000000000000000 : ℝ)^4943 := by
      have hnat : (400124392404910479 : ℕ)^1024*2000000000000000^4943 ≤ 2000128836762823^4943*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400124392404910479 400000000000000000 2000128836762823 2000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000128836762823/2000000000000000 : ℝ)) (X := (400124392404910479/400000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1033353983056743/50000000000000000000 : ℝ) ≤ ((201979990641313579/202000000000000000 : ℝ)+2*(5585566937/11110000000000 : ℝ)*(10703/100000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (201979990641313579/202000000000000000 : ℝ)+2*(5585566937/11110000000000 : ℝ)*(10703/100000 : ℝ)=(2000017125424083/2000000000000000 : ℝ) by norm_num, show 1+2*(1033353983056743/50000000000000000000 : ℝ)=(25001033353983056743/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(124392404910479/800000000000000000 : ℝ)+(1033353983056743/50000000000000000000 : ℝ) ≤ ((201979990641313579/202000000000000000 : ℝ)+(5585566937/11110000000000 : ℝ)*((8129/50000 : ℝ)+(10703/100000 : ℝ)))^(4943/1024 : ℝ) := by
    rw [show (201979990641313579/202000000000000000 : ℝ)+(5585566937/11110000000000 : ℝ)*((8129/50000 : ℝ)+(10703/100000 : ℝ))=(2000072981093453/2000000000000000 : ℝ) by norm_num, show 1+(124392404910479/800000000000000000 : ℝ)+(1033353983056743/50000000000000000000 : ℝ)=(100017615758579923361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(124392404910479/800000000000000000 : ℝ) ≤ ((201979990641313579/202000000000000000 : ℝ)+2*(5585566937/11110000000000 : ℝ)*(8129/50000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (201979990641313579/202000000000000000 : ℝ)+2*(5585566937/11110000000000 : ℝ)*(8129/50000 : ℝ)=(2000128836762823/2000000000000000 : ℝ) by norm_num, show 1+2*(124392404910479/800000000000000000 : ℝ)=(400124392404910479/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (201979990641313579/202000000000000000 : ℝ)*(X 1 0+X 2 0)+(5585566937/11110000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (10703/100000 : ℝ)) (hi := (8129/50000 : ℝ)) (c := (201979990641313579/202000000000000000 : ℝ)) (alpha := (5585566937/11110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (201979990641313579/202000000000000000 : ℝ)*(X 0 1+X 2 1)+(5585566937/11110000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (10703/100000 : ℝ)) (hi := (8129/50000 : ℝ)) (c := (201979990641313579/202000000000000000 : ℝ)) (alpha := (5585566937/11110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (201979990641313579/202000000000000000 : ℝ)*(X 0 2+X 1 2)+(5585566937/11110000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (10703/100000 : ℝ)) (hi := (8129/50000 : ℝ)) (c := (201979990641313579/202000000000000000 : ℝ)) (alpha := (5585566937/11110000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-99548237/625000000 : ℝ)*X 0 0+(2722665531/5000000000 : ℝ)*X 0 1+(5184467049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213865871/400000000 : ℝ)*X 1 0+(-345404201/2000000000 : ℝ)*X 1 1+(103689341/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346646749/10000000000 : ℝ)*X 2 0+(1296116769/2500000000 : ℝ)*X 2 1+(-1727021003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4175411747/10000000000 : ℝ)*X 0 0+(38449371/100000000 : ℝ)*X 0 1+(4525813047/10000000000 : ℝ)*X 0 2+(4175411747/10000000000 : ℝ)*X 1 0+(38449371/100000000 : ℝ)*X 1 1+(4525813047/10000000000 : ℝ)*X 1 2+(4175411747/10000000000 : ℝ)*X 2 0+(38449371/100000000 : ℝ)*X 2 1+(4525813047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-99552183/625000000 : ℝ)*X 0 0+(324152823/625000000 : ℝ)*X 0 1+(544333213/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276900369/10000000000 : ℝ)*X 1 0+(-73407797/500000000 : ℝ)*X 1 1+(1088666441/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659612529/1250000000 : ℝ)*X 2 0+(5443332341/10000000000 : ℝ)*X 2 1+(-1468155941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087788357/5000000000 : ℝ)*X 0 0+(904130007/2000000000 : ℝ)*X 0 1+(481269287/1250000000 : ℝ)*X 0 2+(2087788357/5000000000 : ℝ)*X 1 0+(904130007/2000000000 : ℝ)*X 1 1+(481269287/1250000000 : ℝ)*X 1 2+(2087788357/5000000000 : ℝ)*X 2 0+(904130007/2000000000 : ℝ)*X 2 1+(481269287/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (277563682493740838763695013/27775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395245637/25000000000000 : ℝ)*(base19) + (740278263/50000000000000 : ℝ)*(base23) + (21863633/50000000000000 : ℝ)*(lower2) + (238799133/100000000000000 : ℝ)*(upper3) + (4468627/2500000000000 : ℝ)*(upper5) + (1325542053628159/50000000000000 : ℝ)*(major0) + (1325542053628159/50000000000000 : ℝ)*(major1) + (1325542053628159/50000000000000 : ℝ)*(major2) + (76668712887039/2000000000000 : ℝ)*(sp0) + (3833454263527963/100000000000000 : ℝ)*(sp1) + (1916727181976993/50000000000000 : ℝ)*(sp2) + (734351899017353/50000000000000 : ℝ)*(sp3) + (20200158561/100000000000000 : ℝ)*(sp4) + (4119428841/50000000000000 : ℝ)*(sp7) + (367178009223097/25000000000000 : ℝ)*(f.failure) + (239590990281907/6250000000000 : ℝ)*(f.sum) + (243504158681/111100000000000000000000000 : ℝ)*base66 + (521159953945018329/111100000000000000000000000000000 : ℝ)*base68 + (292072411212618329/111100000000000000000000000000000 : ℝ)*base70 + (363988121255718329/111100000000000000000000000000000 : ℝ)*base72 + (5199602139773/1111000000000000000000000000 : ℝ)*base74 + (40410040550381671/111100000000000000000000000000000 : ℝ)*base75 + (201362406453618329/111100000000000000000000000000000 : ℝ)*base78 + (728740392491818329/111100000000000000000000000000000 : ℝ)*base80 + (162038134069/277750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (33895873/2500000000000000000000 : ℝ)*base89 + (33895873/2500000000000000000000 : ℝ)*base91 + (33895873/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (434954665621329430205337561/55550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (207541863/20000000000000 : ℝ)*(base19) + (1068858397/100000000000000 : ℝ)*(base23) + (316389759/100000000000000 : ℝ)*(lower1) + (1160347/625000000000 : ℝ)*(upper3) + (58485469/100000000000000 : ℝ)*(lower4) + (10208621/6250000000000 : ℝ)*(upper5) + (2692088847942677/100000000000000 : ℝ)*(major0) + (2692088847942677/100000000000000 : ℝ)*(major1) + (2692088847942677/100000000000000 : ℝ)*(major2) + (1617605693/100000000000000 : ℝ)*(sp2) + (389274859468673/10000000000000 : ℝ)*(sp4) + (486593444622177/12500000000000 : ℝ)*(sp5) + (1946372954111321/50000000000000 : ℝ)*(sp6) + (372857210049927/25000000000000 : ℝ)*(sp7) + (372857210049927/25000000000000 : ℝ)*(f.failure) + (389274859468673/10000000000000 : ℝ)*(f.sum) + (1597536886647/555500000000000000000000000 : ℝ)*base66 + (864165383456620813/222200000000000000000000000000000 : ℝ)*base67 + (2458168178791020813/222200000000000000000000000000000 : ℝ)*base69 + (10715678890025420813/222200000000000000000000000000000 : ℝ)*base71 + (796863999721/555500000000000000000000000 : ℝ)*base74 + (7729452690955020813/222200000000000000000000000000000 : ℝ)*base75 + (737848217992020813/222200000000000000000000000000000 : ℝ)*base77 + (1591924083033379187/222200000000000000000000000000000 : ℝ)*base80 + (2142764283961/1111000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (11342657/2500000000000000000000 : ℝ)*base90 + (11342657/2500000000000000000000 : ℝ)*base92 + (11342657/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1657_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8129/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10703/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5353/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1657_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1657_box_0 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-334318613/2500000000 : ℝ)*x 0 + (5406347969/10000000000 : ℝ)*x 1 + (2703174601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334318613/2500000000 : ℝ)^4947 ≤ (3954690584701/50000000000000 : ℝ)^3923 := by
    have hnat : (334318613 : ℕ)^4947*50000000000000^3923 ≤ 3954690584701^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334318613 2500000000 3954690584701 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406347969/10000000000 : ℝ)^4947 ≤ (46045302790503/100000000000000 : ℝ)^3923 := by
    have hnat : (5406347969 : ℕ)^4947*100000000000000^3923 ≤ 46045302790503^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406347969 10000000000 46045302790503 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703174601/5000000000 : ℝ)^4947 ≤ (2877832252059/6250000000000 : ℝ)^3923 := by
    have hnat : (2703174601 : ℕ)^4947*6250000000000^3923 ≤ 2877832252059^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703174601 5000000000 2877832252059 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-334318613/2500000000 : ℝ), (5406347969/10000000000 : ℝ), (2703174601/5000000000 : ℝ)] ![(3954690584701/50000000000000 : ℝ), (46045302790503/100000000000000 : ℝ), (2877832252059/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-334318613/2500000000 : ℝ)|^4947 ≤ (3954690584701/50000000000000 : ℝ)^3923
        have hw : |(-334318613/2500000000 : ℝ)|=(334318613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406347969/10000000000 : ℝ)|^4947 ≤ (46045302790503/100000000000000 : ℝ)^3923
        have hw : |(5406347969/10000000000 : ℝ)|=(5406347969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703174601/5000000000 : ℝ)|^4947 ≤ (2877832252059/6250000000000 : ℝ)^3923
        have hw : |(2703174601/5000000000 : ℝ)|=(2703174601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_1 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625484093/5000000000 : ℝ)*x 0 + (-777847437/5000000000 : ℝ)*x 1 + (5406348259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625484093/5000000000 : ℝ)^4947 ≤ (2773926612047/6250000000000 : ℝ)^3923 := by
    have hnat : (2625484093 : ℕ)^4947*6250000000000^3923 ≤ 2773926612047^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625484093 5000000000 2773926612047 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777847437/5000000000 : ℝ)^4947 ≤ (2392967072651/25000000000000 : ℝ)^3923 := by
    have hnat : (777847437 : ℕ)^4947*25000000000000^3923 ≤ 2392967072651^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777847437 5000000000 2392967072651 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406348259/10000000000 : ℝ)^4947 ≤ (11511326476277/25000000000000 : ℝ)^3923 := by
    have hnat : (5406348259 : ℕ)^4947*25000000000000^3923 ≤ 11511326476277^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406348259 10000000000 11511326476277 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625484093/5000000000 : ℝ), (-777847437/5000000000 : ℝ), (5406348259/10000000000 : ℝ)] ![(2773926612047/6250000000000 : ℝ), (2392967072651/25000000000000 : ℝ), (11511326476277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625484093/5000000000 : ℝ)|^4947 ≤ (2773926612047/6250000000000 : ℝ)^3923
        have hw : |(2625484093/5000000000 : ℝ)|=(2625484093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-777847437/5000000000 : ℝ)|^4947 ≤ (2392967072651/25000000000000 : ℝ)^3923
        have hw : |(-777847437/5000000000 : ℝ)|=(777847437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406348259/10000000000 : ℝ)|^4947 ≤ (11511326476277/25000000000000 : ℝ)^3923
        have hw : |(5406348259/10000000000 : ℝ)|=(5406348259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_2 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656370987/1250000000 : ℝ)*x 0 + (5406349013/10000000000 : ℝ)*x 1 + (-1555694229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656370987/1250000000 : ℝ)^4947 ≤ (8876564540353/20000000000000 : ℝ)^3923 := by
    have hnat : (656370987 : ℕ)^4947*20000000000000^3923 ≤ 8876564540353^3923*1250000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656370987 1250000000 8876564540353 20000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406349013/10000000000 : ℝ)^4947 ≤ (46045314003081/100000000000000 : ℝ)^3923 := by
    have hnat : (5406349013 : ℕ)^4947*100000000000000^3923 ≤ 46045314003081^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406349013 10000000000 46045314003081 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1555694229/10000000000 : ℝ)^4947 ≤ (9571863286163/100000000000000 : ℝ)^3923 := by
    have hnat : (1555694229 : ℕ)^4947*100000000000000^3923 ≤ 9571863286163^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555694229 10000000000 9571863286163 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656370987/1250000000 : ℝ), (5406349013/10000000000 : ℝ), (-1555694229/10000000000 : ℝ)] ![(8876564540353/20000000000000 : ℝ), (46045314003081/100000000000000 : ℝ), (9571863286163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656370987/1250000000 : ℝ)|^4947 ≤ (8876564540353/20000000000000 : ℝ)^3923
        have hw : |(656370987/1250000000 : ℝ)|=(656370987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406349013/10000000000 : ℝ)|^4947 ≤ (46045314003081/100000000000000 : ℝ)^3923
        have hw : |(5406349013/10000000000 : ℝ)|=(5406349013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1555694229/10000000000 : ℝ)|^4947 ≤ (9571863286163/100000000000000 : ℝ)^3923
        have hw : |(-1555694229/10000000000 : ℝ)|=(1555694229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_3 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4451758901/10000000000 : ℝ)*x 0 + (126535831/312500000 : ℝ)*x 1 + (4049146917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4451758901/10000000000 : ℝ)^4947 ≤ (36040408283807/100000000000000 : ℝ)^3923 := by
    have hnat : (4451758901 : ℕ)^4947*100000000000000^3923 ≤ 36040408283807^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4451758901 10000000000 36040408283807 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126535831/312500000 : ℝ)^4947 ≤ (31979794233187/100000000000000 : ℝ)^3923 := by
    have hnat : (126535831 : ℕ)^4947*100000000000000^3923 ≤ 31979794233187^3923*312500000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126535831 312500000 31979794233187 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4049146917/10000000000 : ℝ)^4947 ≤ (31979797470011/100000000000000 : ℝ)^3923 := by
    have hnat : (4049146917 : ℕ)^4947*100000000000000^3923 ≤ 31979797470011^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049146917 10000000000 31979797470011 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4451758901/10000000000 : ℝ), (126535831/312500000 : ℝ), (4049146917/10000000000 : ℝ)] ![(36040408283807/100000000000000 : ℝ), (31979794233187/100000000000000 : ℝ), (31979797470011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4451758901/10000000000 : ℝ)|^4947 ≤ (36040408283807/100000000000000 : ℝ)^3923
        have hw : |(4451758901/10000000000 : ℝ)|=(4451758901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126535831/312500000 : ℝ)|^4947 ≤ (31979794233187/100000000000000 : ℝ)^3923
        have hw : |(126535831/312500000 : ℝ)|=(126535831/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4049146917/10000000000 : ℝ)|^4947 ≤ (31979797470011/100000000000000 : ℝ)^3923
        have hw : |(4049146917/10000000000 : ℝ)|=(4049146917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_4 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464711421/2500000000 : ℝ)*x 0 + (5215905917/10000000000 : ℝ)*x 1 + (2607952661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464711421/2500000000 : ℝ)^4947 ≤ (11981129981373/100000000000000 : ℝ)^3923 := by
    have hnat : (464711421 : ℕ)^4947*100000000000000^3923 ≤ 11981129981373^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464711421 2500000000 11981129981373 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215905917/10000000000 : ℝ)^4947 ≤ (5501179771221/12500000000000 : ℝ)^3923 := by
    have hnat : (5215905917 : ℕ)^4947*12500000000000^3923 ≤ 5501179771221^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215905917 10000000000 5501179771221 12500000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607952661/5000000000 : ℝ)^4947 ≤ (44009431838997/100000000000000 : ℝ)^3923 := by
    have hnat : (2607952661 : ℕ)^4947*100000000000000^3923 ≤ 44009431838997^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607952661 5000000000 44009431838997 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464711421/2500000000 : ℝ), (5215905917/10000000000 : ℝ), (2607952661/5000000000 : ℝ)] ![(11981129981373/100000000000000 : ℝ), (5501179771221/12500000000000 : ℝ), (44009431838997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464711421/2500000000 : ℝ)|^4947 ≤ (11981129981373/100000000000000 : ℝ)^3923
        have hw : |(-464711421/2500000000 : ℝ)|=(464711421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215905917/10000000000 : ℝ)|^4947 ≤ (5501179771221/12500000000000 : ℝ)^3923
        have hw : |(5215905917/10000000000 : ℝ)|=(5215905917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607952661/5000000000 : ℝ)|^4947 ≤ (44009431838997/100000000000000 : ℝ)^3923
        have hw : |(2607952661/5000000000 : ℝ)|=(2607952661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_5 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690780781/5000000000 : ℝ)*x 0 + (-1637554261/10000000000 : ℝ)*x 1 + (521590579/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690780781/5000000000 : ℝ)^4947 ≤ (45779255842231/100000000000000 : ℝ)^3923 := by
    have hnat : (2690780781 : ℕ)^4947*100000000000000^3923 ≤ 45779255842231^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690780781 5000000000 45779255842231 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1637554261/10000000000 : ℝ)^4947 ≤ (10211307325969/100000000000000 : ℝ)^3923 := by
    have hnat : (1637554261 : ℕ)^4947*100000000000000^3923 ≤ 10211307325969^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637554261 10000000000 10211307325969 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521590579/1000000000 : ℝ)^4947 ≤ (22004718409247/50000000000000 : ℝ)^3923 := by
    have hnat : (521590579 : ℕ)^4947*50000000000000^3923 ≤ 22004718409247^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521590579 1000000000 22004718409247 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690780781/5000000000 : ℝ), (-1637554261/10000000000 : ℝ), (521590579/1000000000 : ℝ)] ![(45779255842231/100000000000000 : ℝ), (10211307325969/100000000000000 : ℝ), (22004718409247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690780781/5000000000 : ℝ)|^4947 ≤ (45779255842231/100000000000000 : ℝ)^3923
        have hw : |(2690780781/5000000000 : ℝ)|=(2690780781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1637554261/10000000000 : ℝ)|^4947 ≤ (10211307325969/100000000000000 : ℝ)^3923
        have hw : |(-1637554261/10000000000 : ℝ)|=(1637554261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521590579/1000000000 : ℝ)|^4947 ≤ (22004718409247/50000000000000 : ℝ)^3923
        have hw : |(521590579/1000000000 : ℝ)|=(521590579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_6 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168173809/312500000 : ℝ)*x 0 + (5215905481/10000000000 : ℝ)*x 1 + (-818777117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168173809/312500000 : ℝ)^4947 ≤ (45779259339279/100000000000000 : ℝ)^3923 := by
    have hnat : (168173809 : ℕ)^4947*100000000000000^3923 ≤ 45779259339279^3923*312500000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168173809 312500000 45779259339279 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215905481/10000000000 : ℝ)^4947 ≤ (44009433530749/100000000000000 : ℝ)^3923 := by
    have hnat : (5215905481 : ℕ)^4947*100000000000000^3923 ≤ 44009433530749^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215905481 10000000000 44009433530749 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (818777117/5000000000 : ℝ)^4947 ≤ (10211307113657/100000000000000 : ℝ)^3923 := by
    have hnat : (818777117 : ℕ)^4947*100000000000000^3923 ≤ 10211307113657^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818777117 5000000000 10211307113657 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168173809/312500000 : ℝ), (5215905481/10000000000 : ℝ), (-818777117/5000000000 : ℝ)] ![(45779259339279/100000000000000 : ℝ), (44009433530749/100000000000000 : ℝ), (10211307113657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168173809/312500000 : ℝ)|^4947 ≤ (45779259339279/100000000000000 : ℝ)^3923
        have hw : |(168173809/312500000 : ℝ)|=(168173809/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215905481/10000000000 : ℝ)|^4947 ≤ (44009433530749/100000000000000 : ℝ)^3923
        have hw : |(5215905481/10000000000 : ℝ)|=(5215905481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-818777117/5000000000 : ℝ)|^4947 ≤ (10211307113657/100000000000000 : ℝ)^3923
        have hw : |(-818777117/5000000000 : ℝ)|=(818777117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_7 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (15569779/40000000 : ℝ)*x 0 + (2164240921/5000000000 : ℝ)*x 1 + (1082120413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15569779/40000000 : ℝ)^4947 ≤ (30427087676259/100000000000000 : ℝ)^3923 := by
    have hnat : (15569779 : ℕ)^4947*100000000000000^3923 ≤ 30427087676259^3923*40000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15569779 40000000 30427087676259 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164240921/5000000000 : ℝ)^4947 ≤ (1087076785043/3125000000000 : ℝ)^3923 := by
    have hnat : (2164240921 : ℕ)^4947*3125000000000^3923 ≤ 1087076785043^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164240921 5000000000 1087076785043 3125000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082120413/2500000000 : ℝ)^4947 ≤ (108707672487/312500000000 : ℝ)^3923 := by
    have hnat : (1082120413 : ℕ)^4947*312500000000^3923 ≤ 108707672487^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082120413 2500000000 108707672487 312500000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(15569779/40000000 : ℝ), (2164240921/5000000000 : ℝ), (1082120413/2500000000 : ℝ)] ![(30427087676259/100000000000000 : ℝ), (1087076785043/3125000000000 : ℝ), (108707672487/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(15569779/40000000 : ℝ)|^4947 ≤ (30427087676259/100000000000000 : ℝ)^3923
        have hw : |(15569779/40000000 : ℝ)|=(15569779/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2164240921/5000000000 : ℝ)|^4947 ≤ (1087076785043/3125000000000 : ℝ)^3923
        have hw : |(2164240921/5000000000 : ℝ)|=(2164240921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082120413/2500000000 : ℝ)|^4947 ≤ (108707672487/312500000000 : ℝ)^3923
        have hw : |(1082120413/2500000000 : ℝ)|=(1082120413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_8 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-174753507/1000000000 : ℝ)*x 0 + (2539389331/5000000000 : ℝ)*x 1 + (5435718247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174753507/1000000000 : ℝ)^4947 ≤ (11083586836599/100000000000000 : ℝ)^3923 := by
    have hnat : (174753507 : ℕ)^4947*100000000000000^3923 ≤ 11083586836599^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174753507 1000000000 11083586836599 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539389331/5000000000 : ℝ)^4947 ≤ (21277724868099/50000000000000 : ℝ)^3923 := by
    have hnat : (2539389331 : ℕ)^4947*50000000000000^3923 ≤ 21277724868099^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539389331 5000000000 21277724868099 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435718247/10000000000 : ℝ)^4947 ≤ (4636096340641/10000000000000 : ℝ)^3923 := by
    have hnat : (5435718247 : ℕ)^4947*10000000000000^3923 ≤ 4636096340641^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435718247 10000000000 4636096340641 10000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174753507/1000000000 : ℝ), (2539389331/5000000000 : ℝ), (5435718247/10000000000 : ℝ)] ![(11083586836599/100000000000000 : ℝ), (21277724868099/50000000000000 : ℝ), (4636096340641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174753507/1000000000 : ℝ)|^4947 ≤ (11083586836599/100000000000000 : ℝ)^3923
        have hw : |(-174753507/1000000000 : ℝ)|=(174753507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539389331/5000000000 : ℝ)|^4947 ≤ (21277724868099/50000000000000 : ℝ)^3923
        have hw : |(2539389331/5000000000 : ℝ)|=(2539389331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435718247/10000000000 : ℝ)|^4947 ≤ (4636096340641/10000000000000 : ℝ)^3923
        have hw : |(5435718247/10000000000 : ℝ)|=(5435718247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_9 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046166067/2000000000 : ℝ)*x 0 + (-1542647299/10000000000 : ℝ)*x 1 + (5435718113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046166067/2000000000 : ℝ)^4947 ≤ (22084146261297/50000000000000 : ℝ)^3923 := by
    have hnat : (1046166067 : ℕ)^4947*50000000000000^3923 ≤ 22084146261297^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046166067 2000000000 22084146261297 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1542647299/10000000000 : ℝ)^4947 ≤ (9470745494429/100000000000000 : ℝ)^3923 := by
    have hnat : (1542647299 : ℕ)^4947*100000000000000^3923 ≤ 9470745494429^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542647299 10000000000 9470745494429 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435718113/10000000000 : ℝ)^4947 ≤ (46360961965211/100000000000000 : ℝ)^3923 := by
    have hnat : (5435718113 : ℕ)^4947*100000000000000^3923 ≤ 46360961965211^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435718113 10000000000 46360961965211 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046166067/2000000000 : ℝ), (-1542647299/10000000000 : ℝ), (5435718113/10000000000 : ℝ)] ![(22084146261297/50000000000000 : ℝ), (9470745494429/100000000000000 : ℝ), (46360961965211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046166067/2000000000 : ℝ)|^4947 ≤ (22084146261297/50000000000000 : ℝ)^3923
        have hw : |(1046166067/2000000000 : ℝ)|=(1046166067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1542647299/10000000000 : ℝ)|^4947 ≤ (9470745494429/100000000000000 : ℝ)^3923
        have hw : |(-1542647299/10000000000 : ℝ)|=(1542647299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435718113/10000000000 : ℝ)|^4947 ≤ (46360961965211/100000000000000 : ℝ)^3923
        have hw : |(5435718113/10000000000 : ℝ)|=(5435718113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_10 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230830039/10000000000 : ℝ)*x 0 + (5435718239/10000000000 : ℝ)*x 1 + (-1542647531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230830039/10000000000 : ℝ)^4947 ≤ (22084144685409/50000000000000 : ℝ)^3923 := by
    have hnat : (5230830039 : ℕ)^4947*50000000000000^3923 ≤ 22084144685409^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230830039 10000000000 22084144685409 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435718239/10000000000 : ℝ)^4947 ≤ (2897560207523/6250000000000 : ℝ)^3923 := by
    have hnat : (5435718239 : ℕ)^4947*6250000000000^3923 ≤ 2897560207523^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435718239 10000000000 2897560207523 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1542647531/10000000000 : ℝ)^4947 ≤ (9470747290523/100000000000000 : ℝ)^3923 := by
    have hnat : (1542647531 : ℕ)^4947*100000000000000^3923 ≤ 9470747290523^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542647531 10000000000 9470747290523 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230830039/10000000000 : ℝ), (5435718239/10000000000 : ℝ), (-1542647531/10000000000 : ℝ)] ![(22084144685409/50000000000000 : ℝ), (2897560207523/6250000000000 : ℝ), (9470747290523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230830039/10000000000 : ℝ)|^4947 ≤ (22084144685409/50000000000000 : ℝ)^3923
        have hw : |(5230830039/10000000000 : ℝ)|=(5230830039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435718239/10000000000 : ℝ)|^4947 ≤ (2897560207523/6250000000000 : ℝ)^3923
        have hw : |(5435718239/10000000000 : ℝ)|=(5435718239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1542647531/10000000000 : ℝ)|^4947 ≤ (9470747290523/100000000000000 : ℝ)^3923
        have hw : |(-1542647531/10000000000 : ℝ)|=(1542647531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_11 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2267819567/5000000000 : ℝ)*x 0 + (2002995191/5000000000 : ℝ)*x 1 + (4005990681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2267819567/5000000000 : ℝ)^4947 ≤ (36898834679817/100000000000000 : ℝ)^3923 := by
    have hnat : (2267819567 : ℕ)^4947*100000000000000^3923 ≤ 36898834679817^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267819567 5000000000 36898834679817 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002995191/5000000000 : ℝ)^4947 ≤ (31550581162121/100000000000000 : ℝ)^3923 := by
    have hnat : (2002995191 : ℕ)^4947*100000000000000^3923 ≤ 31550581162121^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002995191 5000000000 31550581162121 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4005990681/10000000000 : ℝ)^4947 ≤ (15775292065841/50000000000000 : ℝ)^3923 := by
    have hnat : (4005990681 : ℕ)^4947*50000000000000^3923 ≤ 15775292065841^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005990681 10000000000 15775292065841 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2267819567/5000000000 : ℝ), (2002995191/5000000000 : ℝ), (4005990681/10000000000 : ℝ)] ![(36898834679817/100000000000000 : ℝ), (31550581162121/100000000000000 : ℝ), (15775292065841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2267819567/5000000000 : ℝ)|^4947 ≤ (36898834679817/100000000000000 : ℝ)^3923
        have hw : |(2267819567/5000000000 : ℝ)|=(2267819567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2002995191/5000000000 : ℝ)|^4947 ≤ (31550581162121/100000000000000 : ℝ)^3923
        have hw : |(2002995191/5000000000 : ℝ)|=(2002995191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4005990681/10000000000 : ℝ)|^4947 ≤ (15775292065841/50000000000000 : ℝ)^3923
        have hw : |(4005990681/10000000000 : ℝ)|=(4005990681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_12 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1446736693/10000000000 : ℝ)*x 0 + (692285919/1250000000 : ℝ)*x 1 + (1299025583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1446736693/10000000000 : ℝ)^4947 ≤ (34937384231/400000000000 : ℝ)^3923 := by
    have hnat : (1446736693 : ℕ)^4947*400000000000^3923 ≤ 34937384231^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446736693 10000000000 34937384231 400000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692285919/1250000000 : ℝ)^4947 ≤ (9493364088611/20000000000000 : ℝ)^3923 := by
    have hnat : (692285919 : ℕ)^4947*20000000000000^3923 ≤ 9493364088611^3923*1250000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692285919 1250000000 9493364088611 20000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299025583/2500000000 : ℝ)^4947 ≤ (4379883348123/10000000000000 : ℝ)^3923 := by
    have hnat : (1299025583 : ℕ)^4947*10000000000000^3923 ≤ 4379883348123^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299025583 2500000000 4379883348123 10000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1446736693/10000000000 : ℝ), (692285919/1250000000 : ℝ), (1299025583/2500000000 : ℝ)] ![(34937384231/400000000000 : ℝ), (9493364088611/20000000000000 : ℝ), (4379883348123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1446736693/10000000000 : ℝ)|^4947 ≤ (34937384231/400000000000 : ℝ)^3923
        have hw : |(-1446736693/10000000000 : ℝ)|=(1446736693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692285919/1250000000 : ℝ)|^4947 ≤ (9493364088611/20000000000000 : ℝ)^3923
        have hw : |(692285919/1250000000 : ℝ)|=(692285919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299025583/2500000000 : ℝ)|^4947 ≤ (4379883348123/10000000000000 : ℝ)^3923
        have hw : |(1299025583/2500000000 : ℝ)|=(1299025583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_13 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395151049/10000000000 : ℝ)*x 0 + (-1645785649/10000000000 : ℝ)*x 1 + (1299025819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395151049/10000000000 : ℝ)^4947 ≤ (45925080208711/100000000000000 : ℝ)^3923 := by
    have hnat : (5395151049 : ℕ)^4947*100000000000000^3923 ≤ 45925080208711^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395151049 10000000000 45925080208711 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1645785649/10000000000 : ℝ)^4947 ≤ (10276076266321/100000000000000 : ℝ)^3923 := by
    have hnat : (1645785649 : ℕ)^4947*100000000000000^3923 ≤ 10276076266321^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645785649 10000000000 10276076266321 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299025819/2500000000 : ℝ)^4947 ≤ (43798843515377/100000000000000 : ℝ)^3923 := by
    have hnat : (1299025819 : ℕ)^4947*100000000000000^3923 ≤ 43798843515377^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299025819 2500000000 43798843515377 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395151049/10000000000 : ℝ), (-1645785649/10000000000 : ℝ), (1299025819/2500000000 : ℝ)] ![(45925080208711/100000000000000 : ℝ), (10276076266321/100000000000000 : ℝ), (43798843515377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395151049/10000000000 : ℝ)|^4947 ≤ (45925080208711/100000000000000 : ℝ)^3923
        have hw : |(5395151049/10000000000 : ℝ)|=(5395151049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1645785649/10000000000 : ℝ)|^4947 ≤ (10276076266321/100000000000000 : ℝ)^3923
        have hw : |(-1645785649/10000000000 : ℝ)|=(1645785649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299025819/2500000000 : ℝ)|^4947 ≤ (43798843515377/100000000000000 : ℝ)^3923
        have hw : |(1299025819/2500000000 : ℝ)|=(1299025819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_14 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697575869/5000000000 : ℝ)*x 0 + (519610259/1000000000 : ℝ)*x 1 + (-329157127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697575869/5000000000 : ℝ)^4947 ≤ (45925087604579/100000000000000 : ℝ)^3923 := by
    have hnat : (2697575869 : ℕ)^4947*100000000000000^3923 ≤ 45925087604579^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697575869 5000000000 45925087604579 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519610259/1000000000 : ℝ)^4947 ≤ (43798836223613/100000000000000 : ℝ)^3923 := by
    have hnat : (519610259 : ℕ)^4947*100000000000000^3923 ≤ 43798836223613^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519610259 1000000000 43798836223613 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329157127/2000000000 : ℝ)^4947 ≤ (1027607615609/10000000000000 : ℝ)^3923 := by
    have hnat : (329157127 : ℕ)^4947*10000000000000^3923 ≤ 1027607615609^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329157127 2000000000 1027607615609 10000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697575869/5000000000 : ℝ), (519610259/1000000000 : ℝ), (-329157127/2000000000 : ℝ)] ![(45925087604579/100000000000000 : ℝ), (43798836223613/100000000000000 : ℝ), (1027607615609/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697575869/5000000000 : ℝ)|^4947 ≤ (45925087604579/100000000000000 : ℝ)^3923
        have hw : |(2697575869/5000000000 : ℝ)|=(2697575869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519610259/1000000000 : ℝ)|^4947 ≤ (43798836223613/100000000000000 : ℝ)^3923
        have hw : |(519610259/1000000000 : ℝ)|=(519610259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-329157127/2000000000 : ℝ)|^4947 ≤ (1027607615609/10000000000000 : ℝ)^3923
        have hw : |(-329157127/2000000000 : ℝ)|=(329157127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_box_15 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (958164079/2500000000 : ℝ)*x 0 + (2178737819/5000000000 : ℝ)*x 1 + (871494869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958164079/2500000000 : ℝ)^4947 ≤ (7459729073863/25000000000000 : ℝ)^3923 := by
    have hnat : (958164079 : ℕ)^4947*25000000000000^3923 ≤ 7459729073863^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958164079 2500000000 7459729073863 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178737819/5000000000 : ℝ)^4947 ≤ (35080548409847/100000000000000 : ℝ)^3923 := by
    have hnat : (2178737819 : ℕ)^4947*100000000000000^3923 ≤ 35080548409847^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178737819 5000000000 35080548409847 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (871494869/2000000000 : ℝ)^4947 ≤ (35080535283209/100000000000000 : ℝ)^3923 := by
    have hnat : (871494869 : ℕ)^4947*100000000000000^3923 ≤ 35080535283209^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871494869 2000000000 35080535283209 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(958164079/2500000000 : ℝ), (2178737819/5000000000 : ℝ), (871494869/2000000000 : ℝ)] ![(7459729073863/25000000000000 : ℝ), (35080548409847/100000000000000 : ℝ), (35080535283209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(958164079/2500000000 : ℝ)|^4947 ≤ (7459729073863/25000000000000 : ℝ)^3923
        have hw : |(958164079/2500000000 : ℝ)|=(958164079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2178737819/5000000000 : ℝ)|^4947 ≤ (35080548409847/100000000000000 : ℝ)^3923
        have hw : |(2178737819/5000000000 : ℝ)|=(2178737819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(871494869/2000000000 : ℝ)|^4947 ≤ (35080535283209/100000000000000 : ℝ)^3923
        have hw : |(871494869/2000000000 : ℝ)|=(871494869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1657_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5353/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65097/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58701/100000 : ℝ) ∧ (81323/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88291/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5353/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5353/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5353/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5353/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5353/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5353/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5353/50000 : ℝ) ^ (4943/1024 : ℝ) ≤ (2069505777519247/100000000000000000000 : ℝ) := by
    have hpowers : (5353/50000 : ℝ)^4943 ≤ (2069505777519247/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5353 : ℕ)^4943*100000000000000000000^1024 ≤ 2069505777519247^1024*50000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5353 50000 2069505777519247 100000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5353/50000 : ℝ)) (X := (2069505777519247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8127/50000 : ℝ) ^ (4943/1024 : ℝ) ≤ (15530592686310761/100000000000000000000 : ℝ) := by
    have hpowers : (8127/50000 : ℝ)^4943 ≤ (15530592686310761/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8127 : ℕ)^4943*100000000000000000000^1024 ≤ 15530592686310761^1024*50000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8127 50000 15530592686310761 100000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8127/50000 : ℝ)) (X := (15530592686310761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002069505777519247/50000000000000000000 : ℝ) ≤ (2000017148607291/2000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (50002069505777519247/50000000000000000000 : ℝ)^1024 ≤ (2000017148607291/2000000000000000 : ℝ)^4943 := by
      have hnat : (50002069505777519247 : ℕ)^1024*2000000000000000^4943 ≤ 2000017148607291^4943*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002069505777519247 50000000000000000000 2000017148607291 2000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000017148607291/2000000000000000 : ℝ)) (X := (50002069505777519247/50000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502200012307978751/12500000000000000000 : ℝ) ≤ (1000036458109501/1000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (12502200012307978751/12500000000000000000 : ℝ)^1024 ≤ (1000036458109501/1000000000000000 : ℝ)^4943 := by
      have hnat : (12502200012307978751 : ℕ)^1024*1000000000000000^4943 ≤ 1000036458109501^4943*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502200012307978751 12500000000000000000 1000036458109501 1000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000036458109501/1000000000000000 : ℝ)) (X := (12502200012307978751/12500000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015530592686310761/50000000000000000000 : ℝ) ≤ (2000128683830713/2000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (50015530592686310761/50000000000000000000 : ℝ)^1024 ≤ (2000128683830713/2000000000000000 : ℝ)^4943 := by
      have hnat : (50015530592686310761 : ℕ)^1024*2000000000000000^4943 ≤ 2000128683830713^4943*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015530592686310761 50000000000000000000 2000128683830713 2000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000128683830713/2000000000000000 : ℝ)) (X := (50015530592686310761/50000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2069505777519247/100000000000000000000 : ℝ) ≤ ((1386862630546411817/1387000000000000000 : ℝ)+2*(55767611711/110960000000000 : ℝ)*(5353/50000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (1386862630546411817/1387000000000000000 : ℝ)+2*(55767611711/110960000000000 : ℝ)*(5353/50000 : ℝ)=(2000017148607291/2000000000000000 : ℝ) by norm_num, show 1+2*(2069505777519247/100000000000000000000 : ℝ)=(50002069505777519247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15530592686310761/100000000000000000000 : ℝ)+(2069505777519247/100000000000000000000 : ℝ) ≤ ((1386862630546411817/1387000000000000000 : ℝ)+(55767611711/110960000000000 : ℝ)*((8127/50000 : ℝ)+(5353/50000 : ℝ)))^(4943/1024 : ℝ) := by
    rw [show (1386862630546411817/1387000000000000000 : ℝ)+(55767611711/110960000000000 : ℝ)*((8127/50000 : ℝ)+(5353/50000 : ℝ))=(1000036458109501/1000000000000000 : ℝ) by norm_num, show 1+(15530592686310761/100000000000000000000 : ℝ)+(2069505777519247/100000000000000000000 : ℝ)=(12502200012307978751/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15530592686310761/100000000000000000000 : ℝ) ≤ ((1386862630546411817/1387000000000000000 : ℝ)+2*(55767611711/110960000000000 : ℝ)*(8127/50000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (1386862630546411817/1387000000000000000 : ℝ)+2*(55767611711/110960000000000 : ℝ)*(8127/50000 : ℝ)=(2000128683830713/2000000000000000 : ℝ) by norm_num, show 1+2*(15530592686310761/100000000000000000000 : ℝ)=(50015530592686310761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1386862630546411817/1387000000000000000 : ℝ)*(X 1 0+X 2 0)+(55767611711/110960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (5353/50000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (1386862630546411817/1387000000000000000 : ℝ)) (alpha := (55767611711/110960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1386862630546411817/1387000000000000000 : ℝ)*(X 0 1+X 2 1)+(55767611711/110960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (5353/50000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (1386862630546411817/1387000000000000000 : ℝ)) (alpha := (55767611711/110960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1386862630546411817/1387000000000000000 : ℝ)*(X 0 2+X 1 2)+(55767611711/110960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (5353/50000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (1386862630546411817/1387000000000000000 : ℝ)) (alpha := (55767611711/110960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-334318613/2500000000 : ℝ)*X 0 0+(5406347969/10000000000 : ℝ)*X 0 1+(2703174601/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625484093/5000000000 : ℝ)*X 1 0+(-777847437/5000000000 : ℝ)*X 1 1+(5406348259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((656370987/1250000000 : ℝ)*X 2 0+(5406349013/10000000000 : ℝ)*X 2 1+(-1555694229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4451758901/10000000000 : ℝ)*X 0 0+(126535831/312500000 : ℝ)*X 0 1+(4049146917/10000000000 : ℝ)*X 0 2+(4451758901/10000000000 : ℝ)*X 1 0+(126535831/312500000 : ℝ)*X 1 1+(4049146917/10000000000 : ℝ)*X 1 2+(4451758901/10000000000 : ℝ)*X 2 0+(126535831/312500000 : ℝ)*X 2 1+(4049146917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-464711421/2500000000 : ℝ)*X 0 0+(5215905917/10000000000 : ℝ)*X 0 1+(2607952661/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2690780781/5000000000 : ℝ)*X 1 0+(-1637554261/10000000000 : ℝ)*X 1 1+(521590579/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((168173809/312500000 : ℝ)*X 2 0+(5215905481/10000000000 : ℝ)*X 2 1+(-818777117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((15569779/40000000 : ℝ)*X 0 0+(2164240921/5000000000 : ℝ)*X 0 1+(1082120413/2500000000 : ℝ)*X 0 2+(15569779/40000000 : ℝ)*X 1 0+(2164240921/5000000000 : ℝ)*X 1 1+(1082120413/2500000000 : ℝ)*X 1 2+(15569779/40000000 : ℝ)*X 2 0+(2164240921/5000000000 : ℝ)*X 2 1+(1082120413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-174753507/1000000000 : ℝ)*X 0 0+(2539389331/5000000000 : ℝ)*X 0 1+(5435718247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1046166067/2000000000 : ℝ)*X 1 0+(-1542647299/10000000000 : ℝ)*X 1 1+(5435718113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230830039/10000000000 : ℝ)*X 2 0+(5435718239/10000000000 : ℝ)*X 2 1+(-1542647531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2267819567/5000000000 : ℝ)*X 0 0+(2002995191/5000000000 : ℝ)*X 0 1+(4005990681/10000000000 : ℝ)*X 0 2+(2267819567/5000000000 : ℝ)*X 1 0+(2002995191/5000000000 : ℝ)*X 1 1+(4005990681/10000000000 : ℝ)*X 1 2+(2267819567/5000000000 : ℝ)*X 2 0+(2002995191/5000000000 : ℝ)*X 2 1+(4005990681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1446736693/10000000000 : ℝ)*X 0 0+(692285919/1250000000 : ℝ)*X 0 1+(1299025583/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5395151049/10000000000 : ℝ)*X 1 0+(-1645785649/10000000000 : ℝ)*X 1 1+(1299025819/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697575869/5000000000 : ℝ)*X 2 0+(519610259/1000000000 : ℝ)*X 2 1+(-329157127/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((958164079/2500000000 : ℝ)*X 0 0+(2178737819/5000000000 : ℝ)*X 0 1+(871494869/2000000000 : ℝ)*X 0 2+(958164079/2500000000 : ℝ)*X 1 0+(2178737819/5000000000 : ℝ)*X 1 1+(871494869/2000000000 : ℝ)*X 1 2+(958164079/2500000000 : ℝ)*X 2 0+(2178737819/5000000000 : ℝ)*X 2 1+(871494869/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65097/100000 : ℝ) ≤ (-11285803602234015043253814538833/17337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2982227/100000000000000 : ℝ)*(upper1) + (47107129/100000000000000 : ℝ)*(upper4) + (7274583/50000000000000 : ℝ)*(upper5) + (886114046610233/50000000000000 : ℝ)*(major0) + (886114046610233/50000000000000 : ℝ)*(major1) + (886114046610233/50000000000000 : ℝ)*(major2) + (2706647343/100000000000000 : ℝ)*(sp2) + (34617779/6250000000000 : ℝ)*(sp3) + (2584326907865459/100000000000000 : ℝ)*(sp4) + (2584331105989973/100000000000000 : ℝ)*(sp5) + (161520607509891/6250000000000 : ℝ)*(sp6) + (245455364572651/25000000000000 : ℝ)*(sp7) + (275947007/5000000000000 : ℝ)*(sp8) + (660407813/50000000000000 : ℝ)*(sp13) + (245455503043767/25000000000000 : ℝ)*(f.failure) + (3230415533507/125000000000 : ℝ)*(f.sum) + (20261007511729/2774000000000000000000000000 : ℝ)*base66 + (25393319202960861/69350000000000000000000000000000 : ℝ)*base67 + (436241455145710861/69350000000000000000000000000000 : ℝ)*base69 + (142695804725789139/69350000000000000000000000000000 : ℝ)*base72 + (3975349283783/2774000000000000000000000000 : ℝ)*base74 + (384476737979910861/69350000000000000000000000000000 : ℝ)*base75 + (349610264155610861/69350000000000000000000000000000 : ℝ)*base77 + (462325364870760861/69350000000000000000000000000000 : ℝ)*base79 + (2272870075367/2774000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4038097/2500000000000000000000 : ℝ)*base90 + (4038097/2500000000000000000000 : ℝ)*base92 + (4038097/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58701/100000 : ℝ) ≤ (1272217283781892193290772680161/2167187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5920199/5000000000000 : ℝ)*(lower3) + (10596053/20000000000000 : ℝ)*(upper4) + (2927133/50000000000000 : ℝ)*(upper5) + (116476535088401/6250000000000 : ℝ)*(major0) + (116476535088401/6250000000000 : ℝ)*(major1) + (116476535088401/6250000000000 : ℝ)*(major2) + (1337609432015943/50000000000000 : ℝ)*(sp0) + (2675225000810467/100000000000000 : ℝ)*(sp1) + (1337607618348377/50000000000000 : ℝ)*(sp2) + (51622617275747/5000000000000 : ℝ)*(sp3) + (124579369/1250000000000 : ℝ)*(sp6) + (185224291/5000000000000 : ℝ)*(sp7) + (6319869/3125000000000 : ℝ)*(sp9) + (1584753597/25000000000000 : ℝ)*(sp12) + (25811401250019/2500000000000 : ℝ)*(f.failure) + (1337612601523137/50000000000000 : ℝ)*(f.sum) + (509795655891/346750000000000000000000000 : ℝ)*base66 + (52653378143609617/8668750000000000000000000000000 : ℝ)*base67 + (96188730248072117/8668750000000000000000000000000 : ℝ)*base69 + (26646786144084617/8668750000000000000000000000000 : ℝ)*base71 + (2147656155673/693500000000000000000000000 : ℝ)*base74 + (17734726913678367/8668750000000000000000000000000 : ℝ)*base75 + (27357061891747117/8668750000000000000000000000000 : ℝ)*base77 + (43428416767084617/8668750000000000000000000000000 : ℝ)*base79 + (447941820797/693500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (826171/250000000000000000000 : ℝ)*base89 + (826171/250000000000000000000 : ℝ)*base91 + (826171/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (81323/100000 : ℝ) ≤ (5639921498486483644856734068669/6935000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (901899/25000000000000 : ℝ)*(upper0) + (10904007/50000000000000 : ℝ)*(upper1) + (52568899/50000000000000 : ℝ)*(upper2) + (195623432138373/10000000000000 : ℝ)*(major0) + (195623432138373/10000000000000 : ℝ)*(major1) + (195623432138373/10000000000000 : ℝ)*(major2) + (14987307181/50000000000000 : ℝ)*(sp1) + (18945378113/100000000000000 : ℝ)*(sp2) + (8341275369/100000000000000 : ℝ)*(sp3) + (944151969/20000000000000 : ℝ)*(sp4) + (1400796587280587/50000000000000 : ℝ)*(sp8) + (87548997522083/3125000000000 : ℝ)*(sp9) + (1400789474971453/50000000000000 : ℝ)*(sp10) + (270938478857731/25000000000000 : ℝ)*(sp11) + (1083762256706293/100000000000000 : ℝ)*(f.failure) + (1400798947660509/50000000000000 : ℝ)*(f.sum) + (971056398453/554800000000000000000000000 : ℝ)*base65 + (100749102031138759/13870000000000000000000000000000 : ℝ)*base68 + (68156075247058759/13870000000000000000000000000000 : ℝ)*base70 + (51613918385098759/13870000000000000000000000000000 : ℝ)*base72 + (10699936209201/2774000000000000000000000000 : ℝ)*base74 + (51859086252718759/13870000000000000000000000000000 : ℝ)*base76 + (130144700101398759/13870000000000000000000000000000 : ℝ)*base78 + (160193743747638759/13870000000000000000000000000000 : ℝ)*base80 + (12418065177181/2774000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (22028637/10000000000000000000000 : ℝ)*base89 + (22028637/10000000000000000000000 : ℝ)*base91 + (22028637/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-88291/100000 : ℝ) ≤ (-15307034331962283699935115306483/17337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161150177/100000000000000 : ℝ)*(lower2) + (11648577/10000000000000 : ℝ)*(upper3) + (1617429/100000000000000 : ℝ)*(upper5) + (1000340284464617/50000000000000 : ℝ)*(major0) + (1000340284464617/50000000000000 : ℝ)*(major1) + (1000340284464617/50000000000000 : ℝ)*(major2) + (2151998501/50000000000000 : ℝ)*(sp0) + (29583496177/100000000000000 : ℝ)*(sp6) + (1811468453/6250000000000 : ℝ)*(sp7) + (2875396319/100000000000000 : ℝ)*(sp8) + (730599454719269/25000000000000 : ℝ)*(sp12) + (1461202499135199/50000000000000 : ℝ)*(sp13) + (2922375414774221/100000000000000 : ℝ)*(sp14) + (1108356686171089/100000000000000 : ℝ)*(sp15) + (34637052177073/3125000000000 : ℝ)*(f.failure) + (1461202499135199/50000000000000 : ℝ)*(f.sum) + (2707920290141/2774000000000000000000000000 : ℝ)*base66 + (106485779498833411/69350000000000000000000000000000 : ℝ)*base68 + (108778398357766589/69350000000000000000000000000000 : ℝ)*base69 + (345712083094833411/69350000000000000000000000000000 : ℝ)*base72 + (15343912143417/2774000000000000000000000000 : ℝ)*base74 + (268392493649883411/69350000000000000000000000000000 : ℝ)*base76 + (226936391633033411/69350000000000000000000000000000 : ℝ)*base78 + (372186549550483411/69350000000000000000000000000000 : ℝ)*base80 + (1907765979173/554800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1864343/312500000000000000000 : ℝ)*base90 + (1864343/312500000000000000000 : ℝ)*base92 + (1864343/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1657_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5353/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65097/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58701/100000 : ℝ) else (81323/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88291/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1657_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1657_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65097/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58701/100000 : ℝ) else (81323/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88291/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1657_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1657_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1657_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65097/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58701/100000 : ℝ) else (81323/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88291/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1657_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
