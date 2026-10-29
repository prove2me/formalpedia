-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1618_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:53:11.176993+00:00
-- url     : https://prove2.me/submissions/8b775781-67de-4663-8b0f-fe711856272c

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
theorem support_rectangle_w1618_s0_0 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-775254109/5000000000 : ℝ)*x 0 + (5826384679/10000000000 : ℝ)*x 1 + (4898945513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (775254109/5000000000 : ℝ)^4791 ≤ (4670755368747/50000000000000 : ℝ)^3767 := by
    have hnat : (775254109 : ℕ)^4791*50000000000000^3767 ≤ 4670755368747^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775254109 5000000000 4670755368747 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5826384679/10000000000 : ℝ)^4791 ≤ (50306787676847/100000000000000 : ℝ)^3767 := by
    have hnat : (5826384679 : ℕ)^4791*100000000000000^3767 ≤ 50306787676847^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5826384679 10000000000 50306787676847 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4898945513/10000000000 : ℝ)^4791 ≤ (40351701579433/100000000000000 : ℝ)^3767 := by
    have hnat : (4898945513 : ℕ)^4791*100000000000000^3767 ≤ 40351701579433^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898945513 10000000000 40351701579433 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-775254109/5000000000 : ℝ), (5826384679/10000000000 : ℝ), (4898945513/10000000000 : ℝ)] ![(4670755368747/50000000000000 : ℝ), (50306787676847/100000000000000 : ℝ), (40351701579433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-775254109/5000000000 : ℝ)|^4791 ≤ (4670755368747/50000000000000 : ℝ)^3767
        have hw : |(-775254109/5000000000 : ℝ)|=(775254109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5826384679/10000000000 : ℝ)|^4791 ≤ (50306787676847/100000000000000 : ℝ)^3767
        have hw : |(5826384679/10000000000 : ℝ)|=(5826384679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4898945513/10000000000 : ℝ)|^4791 ≤ (40351701579433/100000000000000 : ℝ)^3767
        have hw : |(4898945513/10000000000 : ℝ)|=(4898945513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s0_1 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2725215919/5000000000 : ℝ)*x 0 + (-1031543437/5000000000 : ℝ)*x 1 + (1224736377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2725215919/5000000000 : ℝ)^4791 ≤ (46215087653077/100000000000000 : ℝ)^3767 := by
    have hnat : (2725215919 : ℕ)^4791*100000000000000^3767 ≤ 46215087653077^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725215919 5000000000 46215087653077 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031543437/5000000000 : ℝ)^4791 ≤ (13433210796071/100000000000000 : ℝ)^3767 := by
    have hnat : (1031543437 : ℕ)^4791*100000000000000^3767 ≤ 13433210796071^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031543437 5000000000 13433210796071 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1224736377/2500000000 : ℝ)^4791 ≤ (20175850763527/50000000000000 : ℝ)^3767 := by
    have hnat : (1224736377 : ℕ)^4791*50000000000000^3767 ≤ 20175850763527^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224736377 2500000000 20175850763527 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2725215919/5000000000 : ℝ), (-1031543437/5000000000 : ℝ), (1224736377/2500000000 : ℝ)] ![(46215087653077/100000000000000 : ℝ), (13433210796071/100000000000000 : ℝ), (20175850763527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2725215919/5000000000 : ℝ)|^4791 ≤ (46215087653077/100000000000000 : ℝ)^3767
        have hw : |(2725215919/5000000000 : ℝ)|=(2725215919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031543437/5000000000 : ℝ)|^4791 ≤ (13433210796071/100000000000000 : ℝ)^3767
        have hw : |(-1031543437/5000000000 : ℝ)|=(1031543437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1224736377/2500000000 : ℝ)|^4791 ≤ (20175850763527/50000000000000 : ℝ)^3767
        have hw : |(1224736377/2500000000 : ℝ)|=(1224736377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s0_2 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2725215829/5000000000 : ℝ)*x 0 + (489894557/1000000000 : ℝ)*x 1 + (-2063087031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2725215829/5000000000 : ℝ)^4791 ≤ (46215085711941/100000000000000 : ℝ)^3767 := by
    have hnat : (2725215829 : ℕ)^4791*100000000000000^3767 ≤ 46215085711941^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725215829 5000000000 46215085711941 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489894557/1000000000 : ℝ)^4791 ≤ (40351702176557/100000000000000 : ℝ)^3767 := by
    have hnat : (489894557 : ℕ)^4791*100000000000000^3767 ≤ 40351702176557^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489894557 1000000000 40351702176557 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063087031/10000000000 : ℝ)^4791 ≤ (6716606048109/50000000000000 : ℝ)^3767 := by
    have hnat : (2063087031 : ℕ)^4791*50000000000000^3767 ≤ 6716606048109^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063087031 10000000000 6716606048109 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2725215829/5000000000 : ℝ), (489894557/1000000000 : ℝ), (-2063087031/10000000000 : ℝ)] ![(46215085711941/100000000000000 : ℝ), (40351702176557/100000000000000 : ℝ), (6716606048109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2725215829/5000000000 : ℝ)|^4791 ≤ (46215085711941/100000000000000 : ℝ)^3767
        have hw : |(2725215829/5000000000 : ℝ)|=(2725215829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(489894557/1000000000 : ℝ)|^4791 ≤ (40351702176557/100000000000000 : ℝ)^3767
        have hw : |(489894557/1000000000 : ℝ)|=(489894557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063087031/10000000000 : ℝ)|^4791 ≤ (6716606048109/50000000000000 : ℝ)^3767
        have hw : |(-2063087031/10000000000 : ℝ)|=(2063087031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s0_3 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (410587343/1000000000 : ℝ)*x 0 + (3075672417/10000000000 : ℝ)*x 1 + (5378734339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410587343/1000000000 : ℝ)^4791 ≤ (32234126657897/100000000000000 : ℝ)^3767 := by
    have hnat : (410587343 : ℕ)^4791*100000000000000^3767 ≤ 32234126657897^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410587343 1000000000 32234126657897 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3075672417/10000000000 : ℝ)^4791 ≤ (1116129547939/5000000000000 : ℝ)^3767 := by
    have hnat : (3075672417 : ℕ)^4791*5000000000000^3767 ≤ 1116129547939^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3075672417 10000000000 1116129547939 5000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378734339/10000000000 : ℝ)^4791 ≤ (45443282364701/100000000000000 : ℝ)^3767 := by
    have hnat : (5378734339 : ℕ)^4791*100000000000000^3767 ≤ 45443282364701^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378734339 10000000000 45443282364701 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(410587343/1000000000 : ℝ), (3075672417/10000000000 : ℝ), (5378734339/10000000000 : ℝ)] ![(32234126657897/100000000000000 : ℝ), (1116129547939/5000000000000 : ℝ), (45443282364701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(410587343/1000000000 : ℝ)|^4791 ≤ (32234126657897/100000000000000 : ℝ)^3767
        have hw : |(410587343/1000000000 : ℝ)|=(410587343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3075672417/10000000000 : ℝ)|^4791 ≤ (1116129547939/5000000000000 : ℝ)^3767
        have hw : |(3075672417/10000000000 : ℝ)|=(3075672417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378734339/10000000000 : ℝ)|^4791 ≤ (45443282364701/100000000000000 : ℝ)^3767
        have hw : |(5378734339/10000000000 : ℝ)|=(5378734339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s0_4 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1553195253/10000000000 : ℝ)*x 0 + (984466181/2000000000 : ℝ)*x 1 + (580217233/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1553195253/10000000000 : ℝ)^4791 ≤ (1872421027651/20000000000000 : ℝ)^3767 := by
    have hnat : (1553195253 : ℕ)^4791*20000000000000^3767 ≤ 1872421027651^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553195253 10000000000 1872421027651 20000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984466181/2000000000 : ℝ)^4791 ≤ (40596842496057/100000000000000 : ℝ)^3767 := by
    have hnat : (984466181 : ℕ)^4791*100000000000000^3767 ≤ 40596842496057^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984466181 2000000000 40596842496057 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580217233/1000000000 : ℝ)^4791 ≤ (50041052351561/100000000000000 : ℝ)^3767 := by
    have hnat : (580217233 : ℕ)^4791*100000000000000^3767 ≤ 50041052351561^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580217233 1000000000 50041052351561 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1553195253/10000000000 : ℝ), (984466181/2000000000 : ℝ), (580217233/1000000000 : ℝ)] ![(1872421027651/20000000000000 : ℝ), (40596842496057/100000000000000 : ℝ), (50041052351561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1553195253/10000000000 : ℝ)|^4791 ≤ (1872421027651/20000000000000 : ℝ)^3767
        have hw : |(-1553195253/10000000000 : ℝ)|=(1553195253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(984466181/2000000000 : ℝ)|^4791 ≤ (40596842496057/100000000000000 : ℝ)^3767
        have hw : |(984466181/2000000000 : ℝ)|=(984466181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(580217233/1000000000 : ℝ)|^4791 ≤ (50041052351561/100000000000000 : ℝ)^3767
        have hw : |(580217233/1000000000 : ℝ)|=(580217233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s0_5 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197159993/10000000000 : ℝ)*x 0 + (-231972039/2000000000 : ℝ)*x 1 + (5802172377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197159993/10000000000 : ℝ)^4791 ≤ (10875307712117/25000000000000 : ℝ)^3767 := by
    have hnat : (5197159993 : ℕ)^4791*25000000000000^3767 ≤ 10875307712117^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197159993 10000000000 10875307712117 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231972039/2000000000 : ℝ)^4791 ≤ (6457716271443/100000000000000 : ℝ)^3767 := by
    have hnat : (231972039 : ℕ)^4791*100000000000000^3767 ≤ 6457716271443^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231972039 2000000000 6457716271443 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5802172377/10000000000 : ℝ)^4791 ≤ (50041052867103/100000000000000 : ℝ)^3767 := by
    have hnat : (5802172377 : ℕ)^4791*100000000000000^3767 ≤ 50041052867103^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5802172377 10000000000 50041052867103 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197159993/10000000000 : ℝ), (-231972039/2000000000 : ℝ), (5802172377/10000000000 : ℝ)] ![(10875307712117/25000000000000 : ℝ), (6457716271443/100000000000000 : ℝ), (50041052867103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197159993/10000000000 : ℝ)|^4791 ≤ (10875307712117/25000000000000 : ℝ)^3767
        have hw : |(5197159993/10000000000 : ℝ)|=(5197159993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-231972039/2000000000 : ℝ)|^4791 ≤ (6457716271443/100000000000000 : ℝ)^3767
        have hw : |(-231972039/2000000000 : ℝ)|=(231972039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5802172377/10000000000 : ℝ)|^4791 ≤ (50041052867103/100000000000000 : ℝ)^3767
        have hw : |(5802172377/10000000000 : ℝ)|=(5802172377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s0_6 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197160001/10000000000 : ℝ)*x 0 + (116043457/200000000 : ℝ)*x 1 + (-23197189/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197160001/10000000000 : ℝ)^4791 ≤ (339853366669/781250000000 : ℝ)^3767 := by
    have hnat : (5197160001 : ℕ)^4791*781250000000^3767 ≤ 339853366669^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197160001 10000000000 339853366669 781250000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116043457/200000000 : ℝ)^4791 ≤ (6255132256929/12500000000000 : ℝ)^3767 := by
    have hnat : (116043457 : ℕ)^4791*12500000000000^3767 ≤ 6255132256929^3767*200000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116043457 200000000 6255132256929 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23197189/200000000 : ℝ)^4791 ≤ (3228855497993/50000000000000 : ℝ)^3767 := by
    have hnat : (23197189 : ℕ)^4791*50000000000000^3767 ≤ 3228855497993^3767*200000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23197189 200000000 3228855497993 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197160001/10000000000 : ℝ), (116043457/200000000 : ℝ), (-23197189/200000000 : ℝ)] ![(339853366669/781250000000 : ℝ), (6255132256929/12500000000000 : ℝ), (3228855497993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197160001/10000000000 : ℝ)|^4791 ≤ (339853366669/781250000000 : ℝ)^3767
        have hw : |(5197160001/10000000000 : ℝ)|=(5197160001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116043457/200000000 : ℝ)|^4791 ≤ (6255132256929/12500000000000 : ℝ)^3767
        have hw : |(116043457/200000000 : ℝ)|=(116043457/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23197189/200000000 : ℝ)|^4791 ≤ (3228855497993/50000000000000 : ℝ)^3767
        have hw : |(-23197189/200000000 : ℝ)|=(23197189/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s0_7 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (514068097/1250000000 : ℝ)*x 0 + (1064132243/2000000000 : ℝ)*x 1 + (3135798089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514068097/1250000000 : ℝ)^4791 ≤ (8075188413323/25000000000000 : ℝ)^3767 := by
    have hnat : (514068097 : ℕ)^4791*25000000000000^3767 ≤ 8075188413323^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514068097 1250000000 8075188413323 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064132243/2000000000 : ℝ)^4791 ≤ (22410092528167/50000000000000 : ℝ)^3767 := by
    have hnat : (1064132243 : ℕ)^4791*50000000000000^3767 ≤ 22410092528167^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064132243 2000000000 22410092528167 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3135798089/10000000000 : ℝ)^4791 ≤ (22879061270767/100000000000000 : ℝ)^3767 := by
    have hnat : (3135798089 : ℕ)^4791*100000000000000^3767 ≤ 22879061270767^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3135798089 10000000000 22879061270767 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(514068097/1250000000 : ℝ), (1064132243/2000000000 : ℝ), (3135798089/10000000000 : ℝ)] ![(8075188413323/25000000000000 : ℝ), (22410092528167/50000000000000 : ℝ), (22879061270767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(514068097/1250000000 : ℝ)|^4791 ≤ (8075188413323/25000000000000 : ℝ)^3767
        have hw : |(514068097/1250000000 : ℝ)|=(514068097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1064132243/2000000000 : ℝ)|^4791 ≤ (22410092528167/50000000000000 : ℝ)^3767
        have hw : |(1064132243/2000000000 : ℝ)|=(1064132243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3135798089/10000000000 : ℝ)|^4791 ≤ (22879061270767/100000000000000 : ℝ)^3767
        have hw : |(3135798089/10000000000 : ℝ)|=(3135798089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1618_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2097/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24059/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4787/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4787 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4787*1^1024 ≤ 0^1024*1^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4787/1024 : ℝ) ≤ (1379457046949303201/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4787 ≤ (1379457046949303201/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4787*100000000000000000000^1024 ≤ 1379457046949303201^1024*5^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1379457046949303201 100000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1379457046949303201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4787 := by
      have hnat : (1 : ℕ)^1024*1^4787 ≤ 1^4787*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101379457046949303201/100000000000000000000 : ℝ) ≤ (1002934964656589/1000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (101379457046949303201/100000000000000000000 : ℝ)^1024 ≤ (1002934964656589/1000000000000000 : ℝ)^4787 := by
      have hnat : (101379457046949303201 : ℕ)^1024*1000000000000000^4787 ≤ 1002934964656589^4787*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101379457046949303201 100000000000000000000 1002934964656589 1000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002934964656589/1000000000000000 : ℝ)) (X := (101379457046949303201/100000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51379457046949303201/50000000000000000000 : ℝ) ≤ (502934964656589/500000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (51379457046949303201/50000000000000000000 : ℝ)^1024 ≤ (502934964656589/500000000000000 : ℝ)^4787 := by
      have hnat : (51379457046949303201 : ℕ)^1024*500000000000000^4787 ≤ 502934964656589^4787*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51379457046949303201 50000000000000000000 502934964656589 500000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502934964656589/500000000000000 : ℝ)) (X := (51379457046949303201/50000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2934964656589/400000000000000 : ℝ)*(0 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2934964656589/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1379457046949303201/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2934964656589/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4787/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2934964656589/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1002934964656589/1000000000000000 : ℝ) by norm_num, show 1+(1379457046949303201/100000000000000000000 : ℝ)+(0 : ℝ)=(101379457046949303201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1379457046949303201/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2934964656589/400000000000000 : ℝ)*(2/5 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2934964656589/400000000000000 : ℝ)*(2/5 : ℝ)=(502934964656589/500000000000000 : ℝ) by norm_num, show 1+2*(1379457046949303201/100000000000000000000 : ℝ)=(51379457046949303201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2934964656589/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2934964656589/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2934964656589/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2934964656589/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2934964656589/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2934964656589/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-775254109/5000000000 : ℝ)*X 0 0+(5826384679/10000000000 : ℝ)*X 0 1+(4898945513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2725215919/5000000000 : ℝ)*X 1 0+(-1031543437/5000000000 : ℝ)*X 1 1+(1224736377/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2725215829/5000000000 : ℝ)*X 2 0+(489894557/1000000000 : ℝ)*X 2 1+(-2063087031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((410587343/1000000000 : ℝ)*X 0 0+(3075672417/10000000000 : ℝ)*X 0 1+(5378734339/10000000000 : ℝ)*X 0 2+(410587343/1000000000 : ℝ)*X 1 0+(3075672417/10000000000 : ℝ)*X 1 1+(5378734339/10000000000 : ℝ)*X 1 2+(410587343/1000000000 : ℝ)*X 2 0+(3075672417/10000000000 : ℝ)*X 2 1+(5378734339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1553195253/10000000000 : ℝ)*X 0 0+(984466181/2000000000 : ℝ)*X 0 1+(580217233/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197159993/10000000000 : ℝ)*X 1 0+(-231972039/2000000000 : ℝ)*X 1 1+(5802172377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5197160001/10000000000 : ℝ)*X 2 0+(116043457/200000000 : ℝ)*X 2 1+(-23197189/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((514068097/1250000000 : ℝ)*X 0 0+(1064132243/2000000000 : ℝ)*X 0 1+(3135798089/10000000000 : ℝ)*X 0 2+(514068097/1250000000 : ℝ)*X 1 0+(1064132243/2000000000 : ℝ)*X 1 1+(3135798089/10000000000 : ℝ)*X 1 2+(514068097/1250000000 : ℝ)*X 2 0+(1064132243/2000000000 : ℝ)*X 2 1+(3135798089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5846461777130193288699/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18811727/100000000000000 : ℝ)*(base1) + (470529039/25000000000000 : ℝ)*(base19) + (184650703/10000000000000 : ℝ)*(base23) + (14684569/5000000000000 : ℝ)*(upper3) + (117050471/50000000000000 : ℝ)*(upper5) + (23632246176003/3125000000000 : ℝ)*(major0) + (23632246176003/3125000000000 : ℝ)*(major1) + (23632246176003/3125000000000 : ℝ)*(major2) + (1078245252172319/100000000000000 : ℝ)*(sp0) + (1078250621084369/100000000000000 : ℝ)*(sp1) + (134781332086687/12500000000000 : ℝ)*(sp2) + (434207580823177/100000000000000 : ℝ)*(sp3) + (7269839933/100000000000000 : ℝ)*(sp4) + (167030873/5000000000000 : ℝ)*(sp7) + (434210940252363/100000000000000 : ℝ)*(f.failure) + (43130100128021/4000000000000 : ℝ)*(f.sum) + (17385604299/78125000000000000000000000 : ℝ)*base65 + (1553593209983/1250000000000000000000000000 : ℝ)*base68 + (7335200783767/1250000000000000000000000000 : ℝ)*base69 + (1113827268767/1250000000000000000000000000 : ℝ)*base71 + (145499060777/156250000000000000000000000 : ℝ)*base74 + (5895130890017/1250000000000000000000000000 : ℝ)*base75 + (535367913733/1250000000000000000000000000 : ℝ)*base78 + (8526696652483/1250000000000000000000000000 : ℝ)*base80 + (185156158087/39062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (92671299/10000000000000000000000 : ℝ)*base90 + (92671299/10000000000000000000000 : ℝ)*base92 + (92671299/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26486425607813657862093/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (358897123/100000000000000 : ℝ)*(base19) + (197327437/25000000000000 : ℝ)*(base23) + (408816843/100000000000000 : ℝ)*(base39) + (15864003/100000000000000 : ℝ)*(upper2) + (132371341/50000000000000 : ℝ)*(upper5) + (398565077810341/50000000000000 : ℝ)*(major0) + (398565077810341/50000000000000 : ℝ)*(major1) + (1245515229381/156250000000 : ℝ)*(major2) + (1727148419/100000000000000 : ℝ)*(sp1) + (162647027/10000000000000 : ℝ)*(sp2) + (56828301194701/5000000000000 : ℝ)*(sp4) + (568281968924239/50000000000000 : ℝ)*(sp5) + (227312803386169/20000000000000 : ℝ)*(sp6) + (457693790242411/100000000000000 : ℝ)*(sp7) + (457693790242411/100000000000000 : ℝ)*(f.failure) + (1136566432710863/100000000000000 : ℝ)*(f.sum) + (86077953717729/20000000000000000000000000000 : ℝ)*base65 + (940853600307/125000000000000000000000000 : ℝ)*base68 + (136396754406849/20000000000000000000000000000 : ℝ)*base69 + (133659440591/62500000000000000000000000 : ℝ)*base72 + (7939967742271/20000000000000000000000000000 : ℝ)*base74 + (114877205246849/20000000000000000000000000000 : ℝ)*base75 + (43515530833151/20000000000000000000000000000 : ℝ)*base78 + (60373892313151/20000000000000000000000000000 : ℝ)*base80 + (12069648396849/10000000000000000000000000000 : ℝ)*base81 + (6149603/10000000000000000000000 : ℝ)*base90 + (6149603/10000000000000000000000 : ℝ)*base92 + (106149603/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1618_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2097/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1618_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1618_s1_0 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1670250007/10000000000 : ℝ)*x 0 + (5522559357/10000000000 : ℝ)*x 1 + (1281313343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1670250007/10000000000 : ℝ)^4791 ≤ (5134247440391/50000000000000 : ℝ)^3767 := by
    have hnat : (1670250007 : ℕ)^4791*50000000000000^3767 ≤ 5134247440391^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670250007 10000000000 5134247440391 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5522559357/10000000000 : ℝ)^4791 ≤ (46994311725243/100000000000000 : ℝ)^3767 := by
    have hnat : (5522559357 : ℕ)^4791*100000000000000^3767 ≤ 46994311725243^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522559357 10000000000 46994311725243 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281313343/2500000000 : ℝ)^4791 ≤ (5342149172001/12500000000000 : ℝ)^3767 := by
    have hnat : (1281313343 : ℕ)^4791*12500000000000^3767 ≤ 5342149172001^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281313343 2500000000 5342149172001 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1670250007/10000000000 : ℝ), (5522559357/10000000000 : ℝ), (1281313343/2500000000 : ℝ)] ![(5134247440391/50000000000000 : ℝ), (46994311725243/100000000000000 : ℝ), (5342149172001/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1670250007/10000000000 : ℝ)|^4791 ≤ (5134247440391/50000000000000 : ℝ)^3767
        have hw : |(-1670250007/10000000000 : ℝ)|=(1670250007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5522559357/10000000000 : ℝ)|^4791 ≤ (46994311725243/100000000000000 : ℝ)^3767
        have hw : |(5522559357/10000000000 : ℝ)|=(5522559357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1281313343/2500000000 : ℝ)|^4791 ≤ (5342149172001/12500000000000 : ℝ)^3767
        have hw : |(1281313343/2500000000 : ℝ)|=(1281313343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s1_1 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369599283/10000000000 : ℝ)*x 0 + (-1877761989/10000000000 : ℝ)*x 1 + (5125253191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369599283/10000000000 : ℝ)^4791 ≤ (5668143219139/12500000000000 : ℝ)^3767 := by
    have hnat : (5369599283 : ℕ)^4791*12500000000000^3767 ≤ 5668143219139^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369599283 10000000000 5668143219139 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1877761989/10000000000 : ℝ)^4791 ≤ (11917662768003/100000000000000 : ℝ)^3767 := by
    have hnat : (1877761989 : ℕ)^4791*100000000000000^3767 ≤ 11917662768003^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877761989 10000000000 11917662768003 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5125253191/10000000000 : ℝ)^4791 ≤ (42737191456457/100000000000000 : ℝ)^3767 := by
    have hnat : (5125253191 : ℕ)^4791*100000000000000^3767 ≤ 42737191456457^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125253191 10000000000 42737191456457 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369599283/10000000000 : ℝ), (-1877761989/10000000000 : ℝ), (5125253191/10000000000 : ℝ)] ![(5668143219139/12500000000000 : ℝ), (11917662768003/100000000000000 : ℝ), (42737191456457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369599283/10000000000 : ℝ)|^4791 ≤ (5668143219139/12500000000000 : ℝ)^3767
        have hw : |(5369599283/10000000000 : ℝ)|=(5369599283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1877761989/10000000000 : ℝ)|^4791 ≤ (11917662768003/100000000000000 : ℝ)^3767
        have hw : |(-1877761989/10000000000 : ℝ)|=(1877761989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5125253191/10000000000 : ℝ)|^4791 ≤ (42737191456457/100000000000000 : ℝ)^3767
        have hw : |(5125253191/10000000000 : ℝ)|=(5125253191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s1_2 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684799677/5000000000 : ℝ)*x 0 + (5125253021/10000000000 : ℝ)*x 1 + (-938881059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684799677/5000000000 : ℝ)^4791 ≤ (22672573257839/50000000000000 : ℝ)^3767 := by
    have hnat : (2684799677 : ℕ)^4791*50000000000000^3767 ≤ 22672573257839^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684799677 5000000000 22672573257839 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125253021/10000000000 : ℝ)^4791 ≤ (42737189653563/100000000000000 : ℝ)^3767 := by
    have hnat : (5125253021 : ℕ)^4791*100000000000000^3767 ≤ 42737189653563^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125253021 10000000000 42737189653563 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938881059/5000000000 : ℝ)^4791 ≤ (11917663809291/100000000000000 : ℝ)^3767 := by
    have hnat : (938881059 : ℕ)^4791*100000000000000^3767 ≤ 11917663809291^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938881059 5000000000 11917663809291 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684799677/5000000000 : ℝ), (5125253021/10000000000 : ℝ), (-938881059/5000000000 : ℝ)] ![(22672573257839/50000000000000 : ℝ), (42737189653563/100000000000000 : ℝ), (11917663809291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684799677/5000000000 : ℝ)|^4791 ≤ (22672573257839/50000000000000 : ℝ)^3767
        have hw : |(2684799677/5000000000 : ℝ)|=(2684799677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125253021/10000000000 : ℝ)|^4791 ≤ (42737189653563/100000000000000 : ℝ)^3767
        have hw : |(5125253021/10000000000 : ℝ)|=(5125253021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-938881059/5000000000 : ℝ)|^4791 ≤ (11917663809291/100000000000000 : ℝ)^3767
        have hw : |(-938881059/5000000000 : ℝ)|=(938881059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s1_3 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048914831/2500000000 : ℝ)*x 0 + (1862176183/5000000000 : ℝ)*x 1 + (294435133/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048914831/2500000000 : ℝ)^4791 ≤ (33133274564547/100000000000000 : ℝ)^3767 := by
    have hnat : (1048914831 : ℕ)^4791*100000000000000^3767 ≤ 33133274564547^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048914831 2500000000 33133274564547 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862176183/5000000000 : ℝ)^4791 ≤ (28473943971227/100000000000000 : ℝ)^3767 := by
    have hnat : (1862176183 : ℕ)^4791*100000000000000^3767 ≤ 28473943971227^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862176183 5000000000 28473943971227 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294435133/625000000 : ℝ)^4791 ≤ (239954884073/625000000000 : ℝ)^3767 := by
    have hnat : (294435133 : ℕ)^4791*625000000000^3767 ≤ 239954884073^3767*625000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294435133 625000000 239954884073 625000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048914831/2500000000 : ℝ), (1862176183/5000000000 : ℝ), (294435133/625000000 : ℝ)] ![(33133274564547/100000000000000 : ℝ), (28473943971227/100000000000000 : ℝ), (239954884073/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048914831/2500000000 : ℝ)|^4791 ≤ (33133274564547/100000000000000 : ℝ)^3767
        have hw : |(1048914831/2500000000 : ℝ)|=(1048914831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1862176183/5000000000 : ℝ)|^4791 ≤ (28473943971227/100000000000000 : ℝ)^3767
        have hw : |(1862176183/5000000000 : ℝ)|=(1862176183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(294435133/625000000 : ℝ)|^4791 ≤ (239954884073/625000000000 : ℝ)^3767
        have hw : |(294435133/625000000 : ℝ)|=(294435133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s1_4 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1670456877/10000000000 : ℝ)*x 0 + (1282378097/2500000000 : ℝ)*x 1 + (2759117759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1670456877/10000000000 : ℝ)^4791 ≤ (2054022488369/20000000000000 : ℝ)^3767 := by
    have hnat : (1670456877 : ℕ)^4791*20000000000000^3767 ≤ 2054022488369^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670456877 10000000000 2054022488369 20000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282378097/2500000000 : ℝ)^4791 ≤ (42782366436899/100000000000000 : ℝ)^3767 := by
    have hnat : (1282378097 : ℕ)^4791*100000000000000^3767 ≤ 42782366436899^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282378097 2500000000 42782366436899 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759117759/5000000000 : ℝ)^4791 ≤ (4694752111177/10000000000000 : ℝ)^3767 := by
    have hnat : (2759117759 : ℕ)^4791*10000000000000^3767 ≤ 4694752111177^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759117759 5000000000 4694752111177 10000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1670456877/10000000000 : ℝ), (1282378097/2500000000 : ℝ), (2759117759/5000000000 : ℝ)] ![(2054022488369/20000000000000 : ℝ), (42782366436899/100000000000000 : ℝ), (4694752111177/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1670456877/10000000000 : ℝ)|^4791 ≤ (2054022488369/20000000000000 : ℝ)^3767
        have hw : |(-1670456877/10000000000 : ℝ)|=(1670456877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282378097/2500000000 : ℝ)|^4791 ≤ (42782366436899/100000000000000 : ℝ)^3767
        have hw : |(1282378097/2500000000 : ℝ)|=(1282378097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2759117759/5000000000 : ℝ)|^4791 ≤ (4694752111177/10000000000000 : ℝ)^3767
        have hw : |(2759117759/5000000000 : ℝ)|=(2759117759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s1_5 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263781787/10000000000 : ℝ)*x 0 + (-742389561/5000000000 : ℝ)*x 1 + (1103647171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263781787/10000000000 : ℝ)^4791 ≤ (22105842462831/50000000000000 : ℝ)^3767 := by
    have hnat : (5263781787 : ℕ)^4791*50000000000000^3767 ≤ 22105842462831^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263781787 10000000000 22105842462831 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742389561/5000000000 : ℝ)^4791 ≤ (8840790299357/100000000000000 : ℝ)^3767 := by
    have hnat : (742389561 : ℕ)^4791*100000000000000^3767 ≤ 8840790299357^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742389561 5000000000 8840790299357 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103647171/2000000000 : ℝ)^4791 ≤ (23473762379121/50000000000000 : ℝ)^3767 := by
    have hnat : (1103647171 : ℕ)^4791*50000000000000^3767 ≤ 23473762379121^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103647171 2000000000 23473762379121 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263781787/10000000000 : ℝ), (-742389561/5000000000 : ℝ), (1103647171/2000000000 : ℝ)] ![(22105842462831/50000000000000 : ℝ), (8840790299357/100000000000000 : ℝ), (23473762379121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263781787/10000000000 : ℝ)|^4791 ≤ (22105842462831/50000000000000 : ℝ)^3767
        have hw : |(5263781787/10000000000 : ℝ)|=(5263781787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-742389561/5000000000 : ℝ)|^4791 ≤ (8840790299357/100000000000000 : ℝ)^3767
        have hw : |(-742389561/5000000000 : ℝ)|=(742389561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103647171/2000000000 : ℝ)|^4791 ≤ (23473762379121/50000000000000 : ℝ)^3767
        have hw : |(1103647171/2000000000 : ℝ)|=(1103647171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s1_6 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631890569/5000000000 : ℝ)*x 0 + (55182361/100000000 : ℝ)*x 1 + (-1484779687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631890569/5000000000 : ℝ)^4791 ≤ (44211677992771/100000000000000 : ℝ)^3767 := by
    have hnat : (2631890569 : ℕ)^4791*100000000000000^3767 ≤ 44211677992771^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631890569 5000000000 44211677992771 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55182361/100000000 : ℝ)^4791 ≤ (23473763704619/50000000000000 : ℝ)^3767 := by
    have hnat : (55182361 : ℕ)^4791*50000000000000^3767 ≤ 23473763704619^3767*100000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55182361 100000000 23473763704619 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1484779687/10000000000 : ℝ)^4791 ≤ (4420397289011/50000000000000 : ℝ)^3767 := by
    have hnat : (1484779687 : ℕ)^4791*50000000000000^3767 ≤ 4420397289011^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1484779687 10000000000 4420397289011 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631890569/5000000000 : ℝ), (55182361/100000000 : ℝ), (-1484779687/10000000000 : ℝ)] ![(44211677992771/100000000000000 : ℝ), (23473763704619/50000000000000 : ℝ), (4420397289011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631890569/5000000000 : ℝ)|^4791 ≤ (44211677992771/100000000000000 : ℝ)^3767
        have hw : |(2631890569/5000000000 : ℝ)|=(2631890569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55182361/100000000 : ℝ)|^4791 ≤ (23473763704619/50000000000000 : ℝ)^3767
        have hw : |(55182361/100000000 : ℝ)|=(55182361/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1484779687/10000000000 : ℝ)|^4791 ≤ (4420397289011/50000000000000 : ℝ)^3767
        have hw : |(-1484779687/10000000000 : ℝ)|=(1484779687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s1_7 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4196171193/10000000000 : ℝ)*x 0 + (470038707/1000000000 : ℝ)*x 1 + (1867544319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196171193/10000000000 : ℝ)^4791 ≤ (16569207859919/50000000000000 : ℝ)^3767 := by
    have hnat : (4196171193 : ℕ)^4791*50000000000000^3767 ≤ 16569207859919^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196171193 10000000000 16569207859919 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (470038707/1000000000 : ℝ)^4791 ≤ (7656640826303/20000000000000 : ℝ)^3767 := by
    have hnat : (470038707 : ℕ)^4791*20000000000000^3767 ≤ 7656640826303^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470038707 1000000000 7656640826303 20000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867544319/5000000000 : ℝ)^4791 ≤ (7144595034817/25000000000000 : ℝ)^3767 := by
    have hnat : (1867544319 : ℕ)^4791*25000000000000^3767 ≤ 7144595034817^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867544319 5000000000 7144595034817 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196171193/10000000000 : ℝ), (470038707/1000000000 : ℝ), (1867544319/5000000000 : ℝ)] ![(16569207859919/50000000000000 : ℝ), (7656640826303/20000000000000 : ℝ), (7144595034817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196171193/10000000000 : ℝ)|^4791 ≤ (16569207859919/50000000000000 : ℝ)^3767
        have hw : |(4196171193/10000000000 : ℝ)|=(4196171193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(470038707/1000000000 : ℝ)|^4791 ≤ (7656640826303/20000000000000 : ℝ)^3767
        have hw : |(470038707/1000000000 : ℝ)|=(470038707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1867544319/5000000000 : ℝ)|^4791 ≤ (7144595034817/25000000000000 : ℝ)^3767
        have hw : |(1867544319/5000000000 : ℝ)|=(1867544319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1618_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2097/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (927/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8847/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2097/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2097/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2097/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2097/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2097/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2097/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2097/50000 : ℝ) ^ (4787/1024 : ℝ) ≤ (1819813633773/5000000000000000000 : ℝ) := by
    have hpowers : (2097/50000 : ℝ)^4787 ≤ (1819813633773/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2097 : ℕ)^4787*5000000000000000000^1024 ≤ 1819813633773^1024*50000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2097 50000 1819813633773 5000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2097/50000 : ℝ)) (X := (1819813633773/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24059/100000 : ℝ) ^ (4787/1024 : ℝ) ≤ (64056543204862767/50000000000000000000 : ℝ) := by
    have hpowers : (24059/100000 : ℝ)^4787 ≤ (64056543204862767/50000000000000000000 : ℝ)^1024 := by
      have hnat : (24059 : ℕ)^4787*50000000000000000000^1024 ≤ 64056543204862767^1024*100000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24059 100000 64056543204862767 50000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24059/100000 : ℝ)) (X := (64056543204862767/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500001819813633773/2500000000000000000 : ℝ) ≤ (5000000778562201/5000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (2500001819813633773/2500000000000000000 : ℝ)^1024 ≤ (5000000778562201/5000000000000000 : ℝ)^4787 := by
      have hnat : (2500001819813633773 : ℕ)^1024*5000000000000000^4787 ≤ 5000000778562201^4787*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500001819813633773 2500000000000000000 5000000778562201 5000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000778562201/5000000000000000 : ℝ)) (X := (2500001819813633773/2500000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50064074741341200497/50000000000000000000 : ℝ) ≤ (10002739900245627/10000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (50064074741341200497/50000000000000000000 : ℝ)^1024 ≤ (10002739900245627/10000000000000000 : ℝ)^4787 := by
      have hnat : (50064074741341200497 : ℕ)^1024*10000000000000000^4787 ≤ 10002739900245627^4787*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064074741341200497 50000000000000000000 10002739900245627 10000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002739900245627/10000000000000000 : ℝ)) (X := (50064074741341200497/50000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25064056543204862767/25000000000000000000 : ℝ) ≤ (2501369560841713/2500000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (25064056543204862767/25000000000000000000 : ℝ)^1024 ≤ (2501369560841713/2500000000000000 : ℝ)^4787 := by
      have hnat : (25064056543204862767 : ℕ)^1024*2500000000000000^4787 ≤ 2501369560841713^4787*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25064056543204862767 25000000000000000000 2501369560841713 2500000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501369560841713/2500000000000000 : ℝ)) (X := (25064056543204862767/25000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1819813633773/5000000000000000000 : ℝ) ≤ ((19862706171017541043/19865000000000000000 : ℝ)+2*(109533724849/79460000000000 : ℝ)*(2097/50000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (19862706171017541043/19865000000000000000 : ℝ)+2*(109533724849/79460000000000 : ℝ)*(2097/50000 : ℝ)=(5000000778562201/5000000000000000 : ℝ) by norm_num, show 1+2*(1819813633773/5000000000000000000 : ℝ)=(2500001819813633773/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64056543204862767/50000000000000000000 : ℝ)+(1819813633773/5000000000000000000 : ℝ) ≤ ((19862706171017541043/19865000000000000000 : ℝ)+(109533724849/79460000000000 : ℝ)*((24059/100000 : ℝ)+(2097/50000 : ℝ)))^(4787/1024 : ℝ) := by
    rw [show (19862706171017541043/19865000000000000000 : ℝ)+(109533724849/79460000000000 : ℝ)*((24059/100000 : ℝ)+(2097/50000 : ℝ))=(10002739900245627/10000000000000000 : ℝ) by norm_num, show 1+(64056543204862767/50000000000000000000 : ℝ)+(1819813633773/5000000000000000000 : ℝ)=(50064074741341200497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64056543204862767/50000000000000000000 : ℝ) ≤ ((19862706171017541043/19865000000000000000 : ℝ)+2*(109533724849/79460000000000 : ℝ)*(24059/100000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (19862706171017541043/19865000000000000000 : ℝ)+2*(109533724849/79460000000000 : ℝ)*(24059/100000 : ℝ)=(2501369560841713/2500000000000000 : ℝ) by norm_num, show 1+2*(64056543204862767/50000000000000000000 : ℝ)=(25064056543204862767/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19862706171017541043/19865000000000000000 : ℝ)*(X 1 0+X 2 0)+(109533724849/79460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (2097/50000 : ℝ)) (hi := (24059/100000 : ℝ)) (c := (19862706171017541043/19865000000000000000 : ℝ)) (alpha := (109533724849/79460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19862706171017541043/19865000000000000000 : ℝ)*(X 0 1+X 2 1)+(109533724849/79460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (2097/50000 : ℝ)) (hi := (24059/100000 : ℝ)) (c := (19862706171017541043/19865000000000000000 : ℝ)) (alpha := (109533724849/79460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19862706171017541043/19865000000000000000 : ℝ)*(X 0 2+X 1 2)+(109533724849/79460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (2097/50000 : ℝ)) (hi := (24059/100000 : ℝ)) (c := (19862706171017541043/19865000000000000000 : ℝ)) (alpha := (109533724849/79460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1670250007/10000000000 : ℝ)*X 0 0+(5522559357/10000000000 : ℝ)*X 0 1+(1281313343/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369599283/10000000000 : ℝ)*X 1 0+(-1877761989/10000000000 : ℝ)*X 1 1+(5125253191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684799677/5000000000 : ℝ)*X 2 0+(5125253021/10000000000 : ℝ)*X 2 1+(-938881059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048914831/2500000000 : ℝ)*X 0 0+(1862176183/5000000000 : ℝ)*X 0 1+(294435133/625000000 : ℝ)*X 0 2+(1048914831/2500000000 : ℝ)*X 1 0+(1862176183/5000000000 : ℝ)*X 1 1+(294435133/625000000 : ℝ)*X 1 2+(1048914831/2500000000 : ℝ)*X 2 0+(1862176183/5000000000 : ℝ)*X 2 1+(294435133/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1670456877/10000000000 : ℝ)*X 0 0+(1282378097/2500000000 : ℝ)*X 0 1+(2759117759/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263781787/10000000000 : ℝ)*X 1 0+(-742389561/5000000000 : ℝ)*X 1 1+(1103647171/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2631890569/5000000000 : ℝ)*X 2 0+(55182361/100000000 : ℝ)*X 2 1+(-1484779687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4196171193/10000000000 : ℝ)*X 0 0+(470038707/1000000000 : ℝ)*X 0 1+(1867544319/5000000000 : ℝ)*X 0 2+(4196171193/10000000000 : ℝ)*X 1 0+(470038707/1000000000 : ℝ)*X 1 1+(1867544319/5000000000 : ℝ)*X 1 2+(4196171193/10000000000 : ℝ)*X 2 0+(470038707/1000000000 : ℝ)*X 2 1+(1867544319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1010202876189626789330652999/124156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129021163/50000000000000 : ℝ)*(base1) + (778951323/50000000000000 : ℝ)*(base19) + (3182367/200000000000 : ℝ)*(base23) + (212651507/100000000000000 : ℝ)*(upper3) + (8946519/6250000000000 : ℝ)*(upper5) + (220659525177781/12500000000000 : ℝ)*(major0) + (220659525177781/12500000000000 : ℝ)*(major1) + (220659525177781/12500000000000 : ℝ)*(major2) + (251696203165999/10000000000000 : ℝ)*(sp0) + (2516969604848457/100000000000000 : ℝ)*(sp1) + (629242392891901/25000000000000 : ℝ)*(sp2) + (40543042835261/4000000000000 : ℝ)*(sp3) + (14670521/156250000000 : ℝ)*(sp4) + (231997569/5000000000000 : ℝ)*(sp7) + (1013580968875231/100000000000000 : ℝ)*(f.failure) + (19663837208993/781250000000 : ℝ)*(f.sum) + (1528538358219/1986500000000000000000000000 : ℝ)*base66 + (1395735222862334417/248312500000000000000000000000000 : ℝ)*base68 + (1348639762588584417/248312500000000000000000000000000 : ℝ)*base70 + (715896785705021917/248312500000000000000000000000000 : ℝ)*base72 + (19568050835469/3973000000000000000000000000 : ℝ)*base74 + (1890306749308228083/248312500000000000000000000000000 : ℝ)*base75 + (482242938675915583/248312500000000000000000000000000 : ℝ)*base77 + (656918758586209417/248312500000000000000000000000000 : ℝ)*base80 + (2859638657689/496625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3622537/10000000000000000000000 : ℝ)*base89 + (3622537/10000000000000000000000 : ℝ)*base91 + (3622537/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36106152384797325964029/3973000000000000000000000000 : ℝ) := by norm_num
    linear_combination (906330677/50000000000000 : ℝ)*(base19) + (48176369/3125000000000 : ℝ)*(base23) + (123719/390625000000 : ℝ)*(upper2) + (178191747/50000000000000 : ℝ)*(upper3) + (97141423/100000000000000 : ℝ)*(upper5) + (902117403299437/50000000000000 : ℝ)*(major0) + (902117403299437/50000000000000 : ℝ)*(major1) + (902117403299437/50000000000000 : ℝ)*(major2) + (2761966467/20000000000000 : ℝ)*(sp1) + (13112940579/100000000000000 : ℝ)*(sp2) + (2572519206892181/100000000000000 : ℝ)*(sp4) + (643125896099623/25000000000000 : ℝ)*(sp5) + (1286252276153897/50000000000000 : ℝ)*(sp6) + (258987525844047/25000000000000 : ℝ)*(sp7) + (258987525844047/25000000000000 : ℝ)*(f.failure) + (2572519206892181/100000000000000 : ℝ)*(f.sum) + (1825752383559/794600000000000000000000000 : ℝ)*base65 + (2453081774861457209/993250000000000000000000000000000 : ℝ)*base68 + (3828543625991957209/993250000000000000000000000000000 : ℝ)*base70 + (650438215002707209/993250000000000000000000000000000 : ℝ)*base72 + (14178116611807/3973000000000000000000000000 : ℝ)*base74 + (437090780995292791/993250000000000000000000000000000 : ℝ)*base75 + (779549244068042791/993250000000000000000000000000000 : ℝ)*base77 + (1067428953372792791/993250000000000000000000000000000 : ℝ)*base79 + (8001446478543/1986500000000000000000000000 : ℝ)*base82 + (14617369/2500000000000000000000 : ℝ)*base89 + (14617369/2500000000000000000000 : ℝ)*base91 + (14617369/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1618_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2097/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (927/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8847/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1618_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1618_s2_0 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-841545359/5000000000 : ℝ)*x 0 + (1365837593/2500000000 : ℝ)*x 1 + (517604267/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841545359/5000000000 : ℝ)^4791 ≤ (1036900219151/10000000000000 : ℝ)^3767 := by
    have hnat : (841545359 : ℕ)^4791*10000000000000^3767 ≤ 1036900219151^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841545359 5000000000 1036900219151 10000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365837593/2500000000 : ℝ)^4791 ≤ (11588611778367/25000000000000 : ℝ)^3767 := by
    have hnat : (1365837593 : ℕ)^4791*25000000000000^3767 ≤ 11588611778367^3767*2500000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365837593 2500000000 11588611778367 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517604267/1000000000 : ℝ)^4791 ≤ (21638275344547/50000000000000 : ℝ)^3767 := by
    have hnat : (517604267 : ℕ)^4791*50000000000000^3767 ≤ 21638275344547^3767*1000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517604267 1000000000 21638275344547 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-841545359/5000000000 : ℝ), (1365837593/2500000000 : ℝ), (517604267/1000000000 : ℝ)] ![(1036900219151/10000000000000 : ℝ), (11588611778367/25000000000000 : ℝ), (21638275344547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-841545359/5000000000 : ℝ)|^4791 ≤ (1036900219151/10000000000000 : ℝ)^3767
        have hw : |(-841545359/5000000000 : ℝ)|=(841545359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365837593/2500000000 : ℝ)|^4791 ≤ (11588611778367/25000000000000 : ℝ)^3767
        have hw : |(1365837593/2500000000 : ℝ)|=(1365837593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517604267/1000000000 : ℝ)|^4791 ≤ (21638275344547/50000000000000 : ℝ)^3767
        have hw : |(517604267/1000000000 : ℝ)|=(517604267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s2_1 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677058641/5000000000 : ℝ)*x 0 + (-1831378537/10000000000 : ℝ)*x 1 + (647005341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677058641/5000000000 : ℝ)^4791 ≤ (22589464227083/50000000000000 : ℝ)^3767 := by
    have hnat : (2677058641 : ℕ)^4791*50000000000000^3767 ≤ 22589464227083^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677058641 5000000000 22589464227083 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1831378537/10000000000 : ℝ)^4791 ≤ (461780808989/4000000000000 : ℝ)^3767 := by
    have hnat : (1831378537 : ℕ)^4791*4000000000000^3767 ≤ 461780808989^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831378537 10000000000 461780808989 4000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647005341/1250000000 : ℝ)^4791 ≤ (865531026117/2000000000000 : ℝ)^3767 := by
    have hnat : (647005341 : ℕ)^4791*2000000000000^3767 ≤ 865531026117^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647005341 1250000000 865531026117 2000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677058641/5000000000 : ℝ), (-1831378537/10000000000 : ℝ), (647005341/1250000000 : ℝ)] ![(22589464227083/50000000000000 : ℝ), (461780808989/4000000000000 : ℝ), (865531026117/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677058641/5000000000 : ℝ)|^4791 ≤ (22589464227083/50000000000000 : ℝ)^3767
        have hw : |(2677058641/5000000000 : ℝ)|=(2677058641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1831378537/10000000000 : ℝ)|^4791 ≤ (461780808989/4000000000000 : ℝ)^3767
        have hw : |(-1831378537/10000000000 : ℝ)|=(1831378537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647005341/1250000000 : ℝ)|^4791 ≤ (865531026117/2000000000000 : ℝ)^3767
        have hw : |(647005341/1250000000 : ℝ)|=(647005341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s2_2 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354117347/10000000000 : ℝ)*x 0 + (5176042597/10000000000 : ℝ)*x 1 + (-14651029/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354117347/10000000000 : ℝ)^4791 ≤ (45178929151743/100000000000000 : ℝ)^3767 := by
    have hnat : (5354117347 : ℕ)^4791*100000000000000^3767 ≤ 45178929151743^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354117347 10000000000 45178929151743 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176042597/10000000000 : ℝ)^4791 ≤ (43276549912833/100000000000000 : ℝ)^3767 := by
    have hnat : (5176042597 : ℕ)^4791*100000000000000^3767 ≤ 43276549912833^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176042597 10000000000 43276549912833 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14651029/80000000 : ℝ)^4791 ≤ (1443065116281/12500000000000 : ℝ)^3767 := by
    have hnat : (14651029 : ℕ)^4791*12500000000000^3767 ≤ 1443065116281^3767*80000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14651029 80000000 1443065116281 12500000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354117347/10000000000 : ℝ), (5176042597/10000000000 : ℝ), (-14651029/80000000 : ℝ)] ![(45178929151743/100000000000000 : ℝ), (43276549912833/100000000000000 : ℝ), (1443065116281/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354117347/10000000000 : ℝ)|^4791 ≤ (45178929151743/100000000000000 : ℝ)^3767
        have hw : |(5354117347/10000000000 : ℝ)|=(5354117347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176042597/10000000000 : ℝ)|^4791 ≤ (43276549912833/100000000000000 : ℝ)^3767
        have hw : |(5176042597/10000000000 : ℝ)|=(5176042597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14651029/80000000 : ℝ)|^4791 ≤ (1443065116281/12500000000000 : ℝ)^3767
        have hw : |(-14651029/80000000 : ℝ)|=(14651029/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s2_3 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42051559/100000000 : ℝ)*x 0 + (154397397/400000000 : ℝ)*x 1 + (2286695507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42051559/100000000 : ℝ)^4791 ≤ (8307171215663/25000000000000 : ℝ)^3767 := by
    have hnat : (42051559 : ℕ)^4791*25000000000000^3767 ≤ 8307171215663^3767*100000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42051559 100000000 8307171215663 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154397397/400000000 : ℝ)^4791 ≤ (5959752391479/20000000000000 : ℝ)^3767 := by
    have hnat : (154397397 : ℕ)^4791*20000000000000^3767 ≤ 5959752391479^3767*400000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154397397 400000000 5959752391479 20000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2286695507/5000000000 : ℝ)^4791 ≤ (9243138292817/25000000000000 : ℝ)^3767 := by
    have hnat : (2286695507 : ℕ)^4791*25000000000000^3767 ≤ 9243138292817^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286695507 5000000000 9243138292817 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42051559/100000000 : ℝ), (154397397/400000000 : ℝ), (2286695507/5000000000 : ℝ)] ![(8307171215663/25000000000000 : ℝ), (5959752391479/20000000000000 : ℝ), (9243138292817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42051559/100000000 : ℝ)|^4791 ≤ (8307171215663/25000000000000 : ℝ)^3767
        have hw : |(42051559/100000000 : ℝ)|=(42051559/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154397397/400000000 : ℝ)|^4791 ≤ (5959752391479/20000000000000 : ℝ)^3767
        have hw : |(154397397/400000000 : ℝ)|=(154397397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2286695507/5000000000 : ℝ)|^4791 ≤ (9243138292817/25000000000000 : ℝ)^3767
        have hw : |(2286695507/5000000000 : ℝ)|=(2286695507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s2_4 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-841584581/5000000000 : ℝ)*x 0 + (1035655347/2000000000 : ℝ)*x 1 + (5461091659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841584581/5000000000 : ℝ)^4791 ≤ (10369616833851/100000000000000 : ℝ)^3767 := by
    have hnat : (841584581 : ℕ)^4791*100000000000000^3767 ≤ 10369616833851^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841584581 5000000000 10369616833851 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035655347/2000000000 : ℝ)^4791 ≤ (43300308510871/100000000000000 : ℝ)^3767 := by
    have hnat : (1035655347 : ℕ)^4791*100000000000000^3767 ≤ 43300308510871^3767*2000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035655347 2000000000 43300308510871 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461091659/10000000000 : ℝ)^4791 ≤ (46330074643319/100000000000000 : ℝ)^3767 := by
    have hnat : (5461091659 : ℕ)^4791*100000000000000^3767 ≤ 46330074643319^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461091659 10000000000 46330074643319 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-841584581/5000000000 : ℝ), (1035655347/2000000000 : ℝ), (5461091659/10000000000 : ℝ)] ![(10369616833851/100000000000000 : ℝ), (43300308510871/100000000000000 : ℝ), (46330074643319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-841584581/5000000000 : ℝ)|^4791 ≤ (10369616833851/100000000000000 : ℝ)^3767
        have hw : |(-841584581/5000000000 : ℝ)|=(841584581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035655347/2000000000 : ℝ)|^4791 ≤ (43300308510871/100000000000000 : ℝ)^3767
        have hw : |(1035655347/2000000000 : ℝ)|=(1035655347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461091659/10000000000 : ℝ)|^4791 ≤ (46330074643319/100000000000000 : ℝ)^3767
        have hw : |(5461091659/10000000000 : ℝ)|=(5461091659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s2_5 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659712553/1250000000 : ℝ)*x 0 + (-1546329723/10000000000 : ℝ)*x 1 + (5461091449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659712553/1250000000 : ℝ)^4791 ≤ (44360423085473/100000000000000 : ℝ)^3767 := by
    have hnat : (659712553 : ℕ)^4791*100000000000000^3767 ≤ 44360423085473^3767*1250000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659712553 1250000000 44360423085473 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1546329723/10000000000 : ℝ)^4791 ≤ (4654752262911/50000000000000 : ℝ)^3767 := by
    have hnat : (1546329723 : ℕ)^4791*50000000000000^3767 ≤ 4654752262911^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546329723 10000000000 4654752262911 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461091449/10000000000 : ℝ)^4791 ≤ (23165036188729/50000000000000 : ℝ)^3767 := by
    have hnat : (5461091449 : ℕ)^4791*50000000000000^3767 ≤ 23165036188729^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461091449 10000000000 23165036188729 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659712553/1250000000 : ℝ), (-1546329723/10000000000 : ℝ), (5461091449/10000000000 : ℝ)] ![(44360423085473/100000000000000 : ℝ), (4654752262911/50000000000000 : ℝ), (23165036188729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659712553/1250000000 : ℝ)|^4791 ≤ (44360423085473/100000000000000 : ℝ)^3767
        have hw : |(659712553/1250000000 : ℝ)|=(659712553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1546329723/10000000000 : ℝ)|^4791 ≤ (4654752262911/50000000000000 : ℝ)^3767
        have hw : |(-1546329723/10000000000 : ℝ)|=(1546329723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461091449/10000000000 : ℝ)|^4791 ≤ (23165036188729/50000000000000 : ℝ)^3767
        have hw : |(5461091449/10000000000 : ℝ)|=(5461091449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s2_6 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638849909/5000000000 : ℝ)*x 0 + (43688743/80000000 : ℝ)*x 1 + (-773164279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638849909/5000000000 : ℝ)^4791 ≤ (44360416607277/100000000000000 : ℝ)^3767 := by
    have hnat : (2638849909 : ℕ)^4791*100000000000000^3767 ≤ 44360416607277^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638849909 5000000000 44360416607277 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43688743/80000000 : ℝ)^4791 ≤ (46330087763737/100000000000000 : ℝ)^3767 := by
    have hnat : (43688743 : ℕ)^4791*100000000000000^3767 ≤ 46330087763737^3767*80000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43688743 80000000 46330087763737 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773164279/5000000000 : ℝ)^4791 ≤ (2327373901373/25000000000000 : ℝ)^3767 := by
    have hnat : (773164279 : ℕ)^4791*25000000000000^3767 ≤ 2327373901373^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773164279 5000000000 2327373901373 25000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638849909/5000000000 : ℝ), (43688743/80000000 : ℝ), (-773164279/5000000000 : ℝ)] ![(44360416607277/100000000000000 : ℝ), (46330087763737/100000000000000 : ℝ), (2327373901373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638849909/5000000000 : ℝ)|^4791 ≤ (44360416607277/100000000000000 : ℝ)^3767
        have hw : |(2638849909/5000000000 : ℝ)|=(2638849909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43688743/80000000 : ℝ)|^4791 ≤ (46330087763737/100000000000000 : ℝ)^3767
        have hw : |(43688743/80000000 : ℝ)|=(43688743/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-773164279/5000000000 : ℝ)|^4791 ≤ (2327373901373/25000000000000 : ℝ)^3767
        have hw : |(-773164279/5000000000 : ℝ)|=(773164279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1618_s2_7 (p : ℝ) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4205350721/10000000000 : ℝ)*x 0 + (2283921189/5000000000 : ℝ)*x 1 + (241596493/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205350721/10000000000 : ℝ)^4791 ≤ (16615321402963/50000000000000 : ℝ)^3767 := by
    have hnat : (4205350721 : ℕ)^4791*50000000000000^3767 ≤ 16615321402963^3767*10000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205350721 10000000000 16615321402963 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283921189/5000000000 : ℝ)^4791 ≤ (36915512286723/100000000000000 : ℝ)^3767 := by
    have hnat : (2283921189 : ℕ)^4791*100000000000000^3767 ≤ 36915512286723^3767*5000000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283921189 5000000000 36915512286723 100000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241596493/625000000 : ℝ)^4791 ≤ (14926922447933/50000000000000 : ℝ)^3767 := by
    have hnat : (241596493 : ℕ)^4791*50000000000000^3767 ≤ 14926922447933^3767*625000000^4791 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241596493 625000000 14926922447933 50000000000000 4791 3767 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4791/1024 : ℝ)) 4791 3767 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205350721/10000000000 : ℝ), (2283921189/5000000000 : ℝ), (241596493/625000000 : ℝ)] ![(16615321402963/50000000000000 : ℝ), (36915512286723/100000000000000 : ℝ), (14926922447933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205350721/10000000000 : ℝ)|^4791 ≤ (16615321402963/50000000000000 : ℝ)^3767
        have hw : |(4205350721/10000000000 : ℝ)|=(4205350721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2283921189/5000000000 : ℝ)|^4791 ≤ (36915512286723/100000000000000 : ℝ)^3767
        have hw : |(2283921189/5000000000 : ℝ)|=(2283921189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241596493/625000000 : ℝ)|^4791 ≤ (14926922447933/50000000000000 : ℝ)^3767
        have hw : |(241596493/625000000 : ℝ)|=(241596493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1618_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8847/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (927/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10367/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16461/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8847/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (927/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8847/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (927/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8847/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (927/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8847/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (927/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8847/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (927/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8847/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (927/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (927/10000 : ℝ) ^ (4787/1024 : ℝ) ≤ (1483540815987699/100000000000000000000 : ℝ) := by
    have hpowers : (927/10000 : ℝ)^4787 ≤ (1483540815987699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (927 : ℕ)^4787*100000000000000000000^1024 ≤ 1483540815987699^1024*10000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        927 10000 1483540815987699 100000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (927/10000 : ℝ)) (X := (1483540815987699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8847/50000 : ℝ) ^ (4787/1024 : ℝ) ≤ (1218410288270427/4000000000000000000 : ℝ) := by
    have hpowers : (8847/50000 : ℝ)^4787 ≤ (1218410288270427/4000000000000000000 : ℝ)^1024 := by
      have hnat : (8847 : ℕ)^4787*4000000000000000000^1024 ≤ 1218410288270427^1024*50000^4787 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8847 50000 1218410288270427 4000000000000000000 4787 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8847/50000 : ℝ)) (X := (1218410288270427/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001483540815987699/50000000000000000000 : ℝ) ≤ (2000012693779651/2000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (50001483540815987699/50000000000000000000 : ℝ)^1024 ≤ (2000012693779651/2000000000000000 : ℝ)^4787 := by
      have hnat : (50001483540815987699 : ℕ)^1024*2000000000000000^4787 ≤ 2000012693779651^4787*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001483540815987699 50000000000000000000 2000012693779651 2000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000012693779651/2000000000000000 : ℝ)) (X := (50001483540815987699/50000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015971899011374187/50000000000000000000 : ℝ) ≤ (5000341616284299/5000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (50015971899011374187/50000000000000000000 : ℝ)^1024 ≤ (5000341616284299/5000000000000000 : ℝ)^4787 := by
      have hnat : (50015971899011374187 : ℕ)^1024*5000000000000000^4787 ≤ 5000341616284299^4787*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015971899011374187 50000000000000000000 5000341616284299 5000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000341616284299/5000000000000000 : ℝ)) (X := (50015971899011374187/50000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001218410288270427/2000000000000000000 : ℝ) ≤ (10001302996238941/10000000000000000 : ℝ) ^ (4787/1024 : ℝ) := by
    have hpowers : (2001218410288270427/2000000000000000000 : ℝ)^1024 ≤ (10001302996238941/10000000000000000 : ℝ)^4787 := by
      have hnat : (2001218410288270427 : ℕ)^1024*10000000000000000^4787 ≤ 10001302996238941^4787*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001218410288270427 2000000000000000000 10001302996238941 10000000000000000 1024 4787 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001302996238941/10000000000000000 : ℝ)) (X := (2001218410288270427/2000000000000000000 : ℝ)) (by norm_num) 4787 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1483540815987699/100000000000000000000 : ℝ) ≤ ((93587826937278601/93600000000000000 : ℝ)+2*(619763670343/842400000000000 : ℝ)*(927/10000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (93587826937278601/93600000000000000 : ℝ)+2*(619763670343/842400000000000 : ℝ)*(927/10000 : ℝ)=(2000012693779651/2000000000000000 : ℝ) by norm_num, show 1+2*(1483540815987699/100000000000000000000 : ℝ)=(50001483540815987699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1218410288270427/4000000000000000000 : ℝ)+(1483540815987699/100000000000000000000 : ℝ) ≤ ((93587826937278601/93600000000000000 : ℝ)+(619763670343/842400000000000 : ℝ)*((8847/50000 : ℝ)+(927/10000 : ℝ)))^(4787/1024 : ℝ) := by
    rw [show (93587826937278601/93600000000000000 : ℝ)+(619763670343/842400000000000 : ℝ)*((8847/50000 : ℝ)+(927/10000 : ℝ))=(5000341616284299/5000000000000000 : ℝ) by norm_num, show 1+(1218410288270427/4000000000000000000 : ℝ)+(1483540815987699/100000000000000000000 : ℝ)=(50015971899011374187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1218410288270427/4000000000000000000 : ℝ) ≤ ((93587826937278601/93600000000000000 : ℝ)+2*(619763670343/842400000000000 : ℝ)*(8847/50000 : ℝ))^(4787/1024 : ℝ) := by
    rw [show (93587826937278601/93600000000000000 : ℝ)+2*(619763670343/842400000000000 : ℝ)*(8847/50000 : ℝ)=(10001302996238941/10000000000000000 : ℝ) by norm_num, show 1+2*(1218410288270427/4000000000000000000 : ℝ)=(2001218410288270427/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (93587826937278601/93600000000000000 : ℝ)*(X 1 0+X 2 0)+(619763670343/842400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (927/10000 : ℝ)) (hi := (8847/50000 : ℝ)) (c := (93587826937278601/93600000000000000 : ℝ)) (alpha := (619763670343/842400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (93587826937278601/93600000000000000 : ℝ)*(X 0 1+X 2 1)+(619763670343/842400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (927/10000 : ℝ)) (hi := (8847/50000 : ℝ)) (c := (93587826937278601/93600000000000000 : ℝ)) (alpha := (619763670343/842400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (93587826937278601/93600000000000000 : ℝ)*(X 0 2+X 1 2)+(619763670343/842400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4787/1024 : ℝ)) (lo := (927/10000 : ℝ)) (hi := (8847/50000 : ℝ)) (c := (93587826937278601/93600000000000000 : ℝ)) (alpha := (619763670343/842400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-841545359/5000000000 : ℝ)*X 0 0+(1365837593/2500000000 : ℝ)*X 0 1+(517604267/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677058641/5000000000 : ℝ)*X 1 0+(-1831378537/10000000000 : ℝ)*X 1 1+(647005341/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354117347/10000000000 : ℝ)*X 2 0+(5176042597/10000000000 : ℝ)*X 2 1+(-14651029/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((42051559/100000000 : ℝ)*X 0 0+(154397397/400000000 : ℝ)*X 0 1+(2286695507/5000000000 : ℝ)*X 0 2+(42051559/100000000 : ℝ)*X 1 0+(154397397/400000000 : ℝ)*X 1 1+(2286695507/5000000000 : ℝ)*X 1 2+(42051559/100000000 : ℝ)*X 2 0+(154397397/400000000 : ℝ)*X 2 1+(2286695507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-841584581/5000000000 : ℝ)*X 0 0+(1035655347/2000000000 : ℝ)*X 0 1+(5461091659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659712553/1250000000 : ℝ)*X 1 0+(-1546329723/10000000000 : ℝ)*X 1 1+(5461091449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638849909/5000000000 : ℝ)*X 2 0+(43688743/80000000 : ℝ)*X 2 1+(-773164279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4205350721/10000000000 : ℝ)*X 0 0+(2283921189/5000000000 : ℝ)*X 0 1+(241596493/625000000 : ℝ)*X 0 2+(4205350721/10000000000 : ℝ)*X 1 0+(2283921189/5000000000 : ℝ)*X 1 1+(241596493/625000000 : ℝ)*X 1 2+(4205350721/10000000000 : ℝ)*X 2 0+(2283921189/5000000000 : ℝ)*X 2 1+(241596493/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1618_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9366163769866862784381731/1404000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (497786463/50000000000000 : ℝ)*(base19) + (29917943/3125000000000 : ℝ)*(base23) + (21538013/50000000000000 : ℝ)*(lower2) + (102654279/50000000000000 : ℝ)*(upper3) + (17332027/20000000000000 : ℝ)*(upper5) + (244112455822847/10000000000000 : ℝ)*(major0) + (244112455822847/10000000000000 : ℝ)*(major1) + (244112455822847/10000000000000 : ℝ)*(major2) + (870150249674479/25000000000000 : ℝ)*(sp0) + (1740305178551799/50000000000000 : ℝ)*(sp1) + (870152598825587/25000000000000 : ℝ)*(sp2) + (1401632138833237/100000000000000 : ℝ)*(sp3) + (647123663/6250000000000 : ℝ)*(sp4) + (1080515723/20000000000000 : ℝ)*(sp7) + (350409385352963/25000000000000 : ℝ)*(f.failure) + (870152838169131/25000000000000 : ℝ)*(f.sum) + (27017979298051/4212000000000000000000000000 : ℝ)*base66 + (56528096639846423/8424000000000000000000000000000 : ℝ)*base67 + (3392575162574423/8424000000000000000000000000000 : ℝ)*base69 + (41647083589670423/8424000000000000000000000000000 : ℝ)*base71 + (693935265893/4212000000000000000000000000 : ℝ)*base73 + (855022470926423/8424000000000000000000000000000 : ℝ)*base75 + (14518011778790423/8424000000000000000000000000000 : ℝ)*base77 + (51862817003270423/8424000000000000000000000000000 : ℝ)*base79 + (5922789224867/842400000000000000000000000 : ℝ)*base82 + (2424901/2500000000000000000000 : ℝ)*base89 + (2424901/2500000000000000000000 : ℝ)*base91 + (2424901/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5053237131863486199206101/585000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1567968727/100000000000000 : ℝ)*(base19) + (14707273/1000000000000 : ℝ)*(base23) + (111546573/50000000000000 : ℝ)*(upper3) + (5776821/10000000000000 : ℝ)*(lower4) + (304381809/100000000000000 : ℝ)*(upper5) + (309986059717389/12500000000000 : ℝ)*(major0) + (309986059717389/12500000000000 : ℝ)*(major1) + (309986059717389/12500000000000 : ℝ)*(major2) + (7267880403/50000000000000 : ℝ)*(sp1) + (28300148493/100000000000000 : ℝ)*(sp2) + (1767940887830293/50000000000000 : ℝ)*(sp4) + (1767932835965527/50000000000000 : ℝ)*(sp5) + (1767926002392397/50000000000000 : ℝ)*(sp6) + (88993430742743/6250000000000 : ℝ)*(sp7) + (88993430742743/6250000000000 : ℝ)*(f.failure) + (1767940887830293/50000000000000 : ℝ)*(f.sum) + (903428340229/1755000000000000000000000000 : ℝ)*base65 + (11062044016052633/3510000000000000000000000000000 : ℝ)*base68 + (32962535783492633/3510000000000000000000000000000 : ℝ)*base70 + (15964907003672633/3510000000000000000000000000000 : ℝ)*base72 + (3072756669191/1755000000000000000000000000 : ℝ)*base74 + (63643529461892633/3510000000000000000000000000000 : ℝ)*base76 + (31594092409922633/3510000000000000000000000000000 : ℝ)*base78 + (59762705603162633/3510000000000000000000000000000 : ℝ)*base80 + (2027796791069/438750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9242961/625000000000000000000 : ℝ)*base89 + (9242961/625000000000000000000 : ℝ)*base91 + (9242961/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1618_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8847/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (927/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1618_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1618_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1618_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1618_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1618_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4787/1024 : ℝ) ≤ p) (hpb : p ≤ (4791/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174162327/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16461/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1618_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
