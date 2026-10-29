-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1735_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:07:33.345379+00:00
-- url     : https://prove2.me/submissions/55015830-1df0-46aa-82fe-d558248d38a5

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
theorem support_rectangle_w1735_s3_0 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-655624927/5000000000 : ℝ)*x 0 + (1379533459/2500000000 : ℝ)*x 1 + (5075885177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655624927/5000000000 : ℝ)^5535 ≤ (8267980884399/100000000000000 : ℝ)^4511 := by
    have hnat : (655624927 : ℕ)^5535*100000000000000^4511 ≤ 8267980884399^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655624927 5000000000 8267980884399 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379533459/2500000000 : ℝ)^5535 ≤ (24107318089411/50000000000000 : ℝ)^4511 := by
    have hnat : (1379533459 : ℕ)^5535*50000000000000^4511 ≤ 24107318089411^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379533459 2500000000 24107318089411 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075885177/10000000000 : ℝ)^5535 ≤ (870347658381/2000000000000 : ℝ)^4511 := by
    have hnat : (5075885177 : ℕ)^5535*2000000000000^4511 ≤ 870347658381^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075885177 10000000000 870347658381 2000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-655624927/5000000000 : ℝ), (1379533459/2500000000 : ℝ), (5075885177/10000000000 : ℝ)] ![(8267980884399/100000000000000 : ℝ), (24107318089411/50000000000000 : ℝ), (870347658381/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-655624927/5000000000 : ℝ)|^5535 ≤ (8267980884399/100000000000000 : ℝ)^4511
        have hw : |(-655624927/5000000000 : ℝ)|=(655624927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379533459/2500000000 : ℝ)|^5535 ≤ (24107318089411/50000000000000 : ℝ)^4511
        have hw : |(1379533459/2500000000 : ℝ)|=(1379533459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075885177/10000000000 : ℝ)|^5535 ≤ (870347658381/2000000000000 : ℝ)^4511
        have hw : |(5075885177/10000000000 : ℝ)|=(5075885177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s3_1 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069376869/2000000000 : ℝ)*x 0 + (-192905969/1250000000 : ℝ)*x 1 + (1268971313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069376869/2000000000 : ℝ)^5535 ≤ (46385205909511/100000000000000 : ℝ)^4511 := by
    have hnat : (1069376869 : ℕ)^5535*100000000000000^4511 ≤ 46385205909511^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069376869 2000000000 46385205909511 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192905969/1250000000 : ℝ)^5535 ≤ (5048705181491/50000000000000 : ℝ)^4511 := by
    have hnat : (192905969 : ℕ)^5535*50000000000000^4511 ≤ 5048705181491^4511*1250000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192905969 1250000000 5048705181491 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268971313/2500000000 : ℝ)^5535 ≤ (21758691854007/50000000000000 : ℝ)^4511 := by
    have hnat : (1268971313 : ℕ)^5535*50000000000000^4511 ≤ 21758691854007^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268971313 2500000000 21758691854007 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069376869/2000000000 : ℝ), (-192905969/1250000000 : ℝ), (1268971313/2500000000 : ℝ)] ![(46385205909511/100000000000000 : ℝ), (5048705181491/50000000000000 : ℝ), (21758691854007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069376869/2000000000 : ℝ)|^5535 ≤ (46385205909511/100000000000000 : ℝ)^4511
        have hw : |(1069376869/2000000000 : ℝ)|=(1069376869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192905969/1250000000 : ℝ)|^5535 ≤ (5048705181491/50000000000000 : ℝ)^4511
        have hw : |(-192905969/1250000000 : ℝ)|=(192905969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1268971313/2500000000 : ℝ)|^5535 ≤ (21758691854007/50000000000000 : ℝ)^4511
        have hw : |(1268971313/2500000000 : ℝ)|=(1268971313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s3_2 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346884339/10000000000 : ℝ)*x 0 + (158621413/312500000 : ℝ)*x 1 + (-1543247807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346884339/10000000000 : ℝ)^5535 ≤ (11596301461411/25000000000000 : ℝ)^4511 := by
    have hnat : (5346884339 : ℕ)^5535*25000000000000^4511 ≤ 11596301461411^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346884339 10000000000 11596301461411 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158621413/312500000 : ℝ)^5535 ≤ (43517383329311/100000000000000 : ℝ)^4511 := by
    have hnat : (158621413 : ℕ)^5535*100000000000000^4511 ≤ 43517383329311^4511*312500000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158621413 312500000 43517383329311 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1543247807/10000000000 : ℝ)^5535 ≤ (5048705402267/50000000000000 : ℝ)^4511 := by
    have hnat : (1543247807 : ℕ)^5535*50000000000000^4511 ≤ 5048705402267^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543247807 10000000000 5048705402267 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346884339/10000000000 : ℝ), (158621413/312500000 : ℝ), (-1543247807/10000000000 : ℝ)] ![(11596301461411/25000000000000 : ℝ), (43517383329311/100000000000000 : ℝ), (5048705402267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346884339/10000000000 : ℝ)|^5535 ≤ (11596301461411/25000000000000 : ℝ)^4511
        have hw : |(5346884339/10000000000 : ℝ)|=(5346884339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158621413/312500000 : ℝ)|^5535 ≤ (43517383329311/100000000000000 : ℝ)^4511
        have hw : |(158621413/312500000 : ℝ)|=(158621413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1543247807/10000000000 : ℝ)|^5535 ≤ (5048705402267/50000000000000 : ℝ)^4511
        have hw : |(-1543247807/10000000000 : ℝ)|=(1543247807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s3_3 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40535709/100000000 : ℝ)*x 0 + (3404930149/10000000000 : ℝ)*x 1 + (1192325961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40535709/100000000 : ℝ)^5535 ≤ (1320920495199/4000000000000 : ℝ)^4511 := by
    have hnat : (40535709 : ℕ)^5535*4000000000000^4511 ≤ 1320920495199^4511*100000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40535709 100000000 1320920495199 4000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3404930149/10000000000 : ℝ)^5535 ≤ (3332778659639/12500000000000 : ℝ)^4511 := by
    have hnat : (3404930149 : ℕ)^5535*12500000000000^4511 ≤ 3332778659639^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3404930149 10000000000 3332778659639 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192325961/2500000000 : ℝ)^5535 ≤ (40314758324979/100000000000000 : ℝ)^4511 := by
    have hnat : (1192325961 : ℕ)^5535*100000000000000^4511 ≤ 40314758324979^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192325961 2500000000 40314758324979 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40535709/100000000 : ℝ), (3404930149/10000000000 : ℝ), (1192325961/2500000000 : ℝ)] ![(1320920495199/4000000000000 : ℝ), (3332778659639/12500000000000 : ℝ), (40314758324979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40535709/100000000 : ℝ)|^5535 ≤ (1320920495199/4000000000000 : ℝ)^4511
        have hw : |(40535709/100000000 : ℝ)|=(40535709/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3404930149/10000000000 : ℝ)|^5535 ≤ (3332778659639/12500000000000 : ℝ)^4511
        have hw : |(3404930149/10000000000 : ℝ)|=(3404930149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192325961/2500000000 : ℝ)|^5535 ≤ (40314758324979/100000000000000 : ℝ)^4511
        have hw : |(1192325961/2500000000 : ℝ)|=(1192325961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s3_4 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3279087/25000000 : ℝ)*x 0 + (5082901793/10000000000 : ℝ)*x 1 + (5510969083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3279087/25000000 : ℝ)^5535 ≤ (8270959216277/100000000000000 : ℝ)^4511 := by
    have hnat : (3279087 : ℕ)^5535*100000000000000^4511 ≤ 8270959216277^4511*25000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3279087 25000000 8270959216277 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082901793/10000000000 : ℝ)^5535 ≤ (43591205903337/100000000000000 : ℝ)^4511 := by
    have hnat : (5082901793 : ℕ)^5535*100000000000000^4511 ≤ 43591205903337^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082901793 10000000000 43591205903337 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510969083/10000000000 : ℝ)^5535 ≤ (12034458715881/25000000000000 : ℝ)^4511 := by
    have hnat : (5510969083 : ℕ)^5535*25000000000000^4511 ≤ 12034458715881^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510969083 10000000000 12034458715881 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3279087/25000000 : ℝ), (5082901793/10000000000 : ℝ), (5510969083/10000000000 : ℝ)] ![(8270959216277/100000000000000 : ℝ), (43591205903337/100000000000000 : ℝ), (12034458715881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3279087/25000000 : ℝ)|^5535 ≤ (8270959216277/100000000000000 : ℝ)^4511
        have hw : |(-3279087/25000000 : ℝ)|=(3279087/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082901793/10000000000 : ℝ)|^5535 ≤ (43591205903337/100000000000000 : ℝ)^4511
        have hw : |(5082901793/10000000000 : ℝ)|=(5082901793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510969083/10000000000 : ℝ)|^5535 ≤ (12034458715881/25000000000000 : ℝ)^4511
        have hw : |(5510969083/10000000000 : ℝ)|=(5510969083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s3_5 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229288491/10000000000 : ℝ)*x 0 + (-1108163943/10000000000 : ℝ)*x 1 + (1377742271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229288491/10000000000 : ℝ)^5535 ≤ (45136604492059/100000000000000 : ℝ)^4511 := by
    have hnat : (5229288491 : ℕ)^5535*100000000000000^4511 ≤ 45136604492059^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229288491 10000000000 45136604492059 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108163943/10000000000 : ℝ)^5535 ≤ (3362780307757/50000000000000 : ℝ)^4511 := by
    have hnat : (1108163943 : ℕ)^5535*50000000000000^4511 ≤ 3362780307757^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108163943 10000000000 3362780307757 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377742271/2500000000 : ℝ)^5535 ≤ (24068917437121/50000000000000 : ℝ)^4511 := by
    have hnat : (1377742271 : ℕ)^5535*50000000000000^4511 ≤ 24068917437121^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377742271 2500000000 24068917437121 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229288491/10000000000 : ℝ), (-1108163943/10000000000 : ℝ), (1377742271/2500000000 : ℝ)] ![(45136604492059/100000000000000 : ℝ), (3362780307757/50000000000000 : ℝ), (24068917437121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229288491/10000000000 : ℝ)|^5535 ≤ (45136604492059/100000000000000 : ℝ)^4511
        have hw : |(5229288491/10000000000 : ℝ)|=(5229288491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1108163943/10000000000 : ℝ)|^5535 ≤ (3362780307757/50000000000000 : ℝ)^4511
        have hw : |(-1108163943/10000000000 : ℝ)|=(1108163943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377742271/2500000000 : ℝ)|^5535 ≤ (24068917437121/50000000000000 : ℝ)^4511
        have hw : |(1377742271/2500000000 : ℝ)|=(1377742271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s3_6 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229288491/10000000000 : ℝ)*x 0 + (1102193817/2000000000 : ℝ)*x 1 + (-554081971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229288491/10000000000 : ℝ)^5535 ≤ (45136604492059/100000000000000 : ℝ)^4511 := by
    have hnat : (5229288491 : ℕ)^5535*100000000000000^4511 ≤ 45136604492059^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229288491 10000000000 45136604492059 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102193817/2000000000 : ℝ)^5535 ≤ (300861468031/625000000000 : ℝ)^4511 := by
    have hnat : (1102193817 : ℕ)^5535*625000000000^4511 ≤ 300861468031^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102193817 2000000000 300861468031 625000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554081971/5000000000 : ℝ)^5535 ≤ (6725560608067/100000000000000 : ℝ)^4511 := by
    have hnat : (554081971 : ℕ)^5535*100000000000000^4511 ≤ 6725560608067^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554081971 5000000000 6725560608067 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229288491/10000000000 : ℝ), (1102193817/2000000000 : ℝ), (-554081971/5000000000 : ℝ)] ![(45136604492059/100000000000000 : ℝ), (300861468031/625000000000 : ℝ), (6725560608067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229288491/10000000000 : ℝ)|^5535 ≤ (45136604492059/100000000000000 : ℝ)^4511
        have hw : |(5229288491/10000000000 : ℝ)|=(5229288491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102193817/2000000000 : ℝ)|^5535 ≤ (300861468031/625000000000 : ℝ)^4511
        have hw : |(1102193817/2000000000 : ℝ)|=(1102193817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554081971/5000000000 : ℝ)|^5535 ≤ (6725560608067/100000000000000 : ℝ)^4511
        have hw : |(-554081971/5000000000 : ℝ)|=(554081971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s3_7 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2027379209/5000000000 : ℝ)*x 0 + (4747657061/10000000000 : ℝ)*x 1 + (685406787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2027379209/5000000000 : ℝ)^5535 ≤ (33034883135267/100000000000000 : ℝ)^4511 := by
    have hnat : (2027379209 : ℕ)^5535*100000000000000^4511 ≤ 33034883135267^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027379209 5000000000 33034883135267 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4747657061/10000000000 : ℝ)^5535 ≤ (5011294769269/12500000000000 : ℝ)^4511 := by
    have hnat : (4747657061 : ℕ)^5535*12500000000000^4511 ≤ 5011294769269^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4747657061 10000000000 5011294769269 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685406787/2000000000 : ℝ)^5535 ≤ (13437379348947/50000000000000 : ℝ)^4511 := by
    have hnat : (685406787 : ℕ)^5535*50000000000000^4511 ≤ 13437379348947^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685406787 2000000000 13437379348947 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2027379209/5000000000 : ℝ), (4747657061/10000000000 : ℝ), (685406787/2000000000 : ℝ)] ![(33034883135267/100000000000000 : ℝ), (5011294769269/12500000000000 : ℝ), (13437379348947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2027379209/5000000000 : ℝ)|^5535 ≤ (33034883135267/100000000000000 : ℝ)^4511
        have hw : |(2027379209/5000000000 : ℝ)|=(2027379209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4747657061/10000000000 : ℝ)|^5535 ≤ (5011294769269/12500000000000 : ℝ)^4511
        have hw : |(4747657061/10000000000 : ℝ)|=(4747657061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685406787/2000000000 : ℝ)|^5535 ≤ (13437379348947/50000000000000 : ℝ)^4511
        have hw : |(685406787/2000000000 : ℝ)|=(685406787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1735_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (731/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1763/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4409/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18271/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (731/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1763/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (731/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1763/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (731/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1763/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (731/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1763/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (731/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1763/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (731/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1763/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1763/20000 : ℝ) ^ (5519/1024 : ℝ) ≤ (206594667199909/100000000000000000000 : ℝ) := by
    have hpowers : (1763/20000 : ℝ)^5519 ≤ (206594667199909/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1763 : ℕ)^5519*100000000000000000000^1024 ≤ 206594667199909^1024*20000^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 20000 206594667199909 100000000000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/20000 : ℝ)) (X := (206594667199909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (731/4000 : ℝ) ^ (5519/1024 : ℝ) ≤ (5255824029301187/50000000000000000000 : ℝ) := by
    have hpowers : (731/4000 : ℝ)^5519 ≤ (5255824029301187/50000000000000000000 : ℝ)^1024 := by
      have hnat : (731 : ℕ)^5519*50000000000000000000^1024 ≤ 5255824029301187^1024*4000^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        731 4000 5255824029301187 50000000000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (731/4000 : ℝ)) (X := (5255824029301187/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000206594667199909/50000000000000000000 : ℝ) ≤ (5000003833168749/5000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (50000206594667199909/50000000000000000000 : ℝ)^1024 ≤ (5000003833168749/5000000000000000 : ℝ)^5519 := by
      have hnat : (50000206594667199909 : ℕ)^1024*5000000000000000^5519 ≤ 5000003833168749^5519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000206594667199909 50000000000000000000 5000003833168749 5000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000003833168749/5000000000000000 : ℝ)) (X := (50000206594667199909/50000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010718242725802283/100000000000000000000 : ℝ) ≤ (10000198858516509/10000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (100010718242725802283/100000000000000000000 : ℝ)^1024 ≤ (10000198858516509/10000000000000000 : ℝ)^5519 := by
      have hnat : (100010718242725802283 : ℕ)^1024*10000000000000000^5519 ≤ 10000198858516509^5519*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010718242725802283 100000000000000000000 10000198858516509 10000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000198858516509/10000000000000000 : ℝ)) (X := (100010718242725802283/100000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005255824029301187/25000000000000000000 : ℝ) ≤ (62502437816847/62500000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (25005255824029301187/25000000000000000000 : ℝ)^1024 ≤ (62502437816847/62500000000000 : ℝ)^5519 := by
      have hnat : (25005255824029301187 : ℕ)^1024*62500000000000^5519 ≤ 62502437816847^5519*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005255824029301187 25000000000000000000 62502437816847 62500000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62502437816847/62500000000000 : ℝ)) (X := (25005255824029301187/25000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(206594667199909/100000000000000000000 : ℝ) ≤ ((43998465956017101/44000000000000000 : ℝ)+2*(191192179011/946000000000000 : ℝ)*(1763/20000 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (43998465956017101/44000000000000000 : ℝ)+2*(191192179011/946000000000000 : ℝ)*(1763/20000 : ℝ)=(5000003833168749/5000000000000000 : ℝ) by norm_num, show 1+2*(206594667199909/100000000000000000000 : ℝ)=(50000206594667199909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5255824029301187/50000000000000000000 : ℝ)+(206594667199909/100000000000000000000 : ℝ) ≤ ((43998465956017101/44000000000000000 : ℝ)+(191192179011/946000000000000 : ℝ)*((731/4000 : ℝ)+(1763/20000 : ℝ)))^(5519/1024 : ℝ) := by
    rw [show (43998465956017101/44000000000000000 : ℝ)+(191192179011/946000000000000 : ℝ)*((731/4000 : ℝ)+(1763/20000 : ℝ))=(10000198858516509/10000000000000000 : ℝ) by norm_num, show 1+(5255824029301187/50000000000000000000 : ℝ)+(206594667199909/100000000000000000000 : ℝ)=(100010718242725802283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5255824029301187/50000000000000000000 : ℝ) ≤ ((43998465956017101/44000000000000000 : ℝ)+2*(191192179011/946000000000000 : ℝ)*(731/4000 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (43998465956017101/44000000000000000 : ℝ)+2*(191192179011/946000000000000 : ℝ)*(731/4000 : ℝ)=(62502437816847/62500000000000 : ℝ) by norm_num, show 1+2*(5255824029301187/50000000000000000000 : ℝ)=(25005255824029301187/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43998465956017101/44000000000000000 : ℝ)*(X 1 0+X 2 0)+(191192179011/946000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (1763/20000 : ℝ)) (hi := (731/4000 : ℝ)) (c := (43998465956017101/44000000000000000 : ℝ)) (alpha := (191192179011/946000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43998465956017101/44000000000000000 : ℝ)*(X 0 1+X 2 1)+(191192179011/946000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (1763/20000 : ℝ)) (hi := (731/4000 : ℝ)) (c := (43998465956017101/44000000000000000 : ℝ)) (alpha := (191192179011/946000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43998465956017101/44000000000000000 : ℝ)*(X 0 2+X 1 2)+(191192179011/946000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (1763/20000 : ℝ)) (hi := (731/4000 : ℝ)) (c := (43998465956017101/44000000000000000 : ℝ)) (alpha := (191192179011/946000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-655624927/5000000000 : ℝ)*X 0 0+(1379533459/2500000000 : ℝ)*X 0 1+(5075885177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069376869/2000000000 : ℝ)*X 1 0+(-192905969/1250000000 : ℝ)*X 1 1+(1268971313/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346884339/10000000000 : ℝ)*X 2 0+(158621413/312500000 : ℝ)*X 2 1+(-1543247807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((40535709/100000000 : ℝ)*X 0 0+(3404930149/10000000000 : ℝ)*X 0 1+(1192325961/2500000000 : ℝ)*X 0 2+(40535709/100000000 : ℝ)*X 1 0+(3404930149/10000000000 : ℝ)*X 1 1+(1192325961/2500000000 : ℝ)*X 1 2+(40535709/100000000 : ℝ)*X 2 0+(3404930149/10000000000 : ℝ)*X 2 1+(1192325961/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-3279087/25000000 : ℝ)*X 0 0+(5082901793/10000000000 : ℝ)*X 0 1+(5510969083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5229288491/10000000000 : ℝ)*X 1 0+(-1108163943/10000000000 : ℝ)*X 1 1+(1377742271/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5229288491/10000000000 : ℝ)*X 2 0+(1102193817/2000000000 : ℝ)*X 2 1+(-554081971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2027379209/5000000000 : ℝ)*X 0 0+(4747657061/10000000000 : ℝ)*X 0 1+(685406787/2000000000 : ℝ)*X 0 2+(2027379209/5000000000 : ℝ)*X 1 0+(4747657061/10000000000 : ℝ)*X 1 1+(685406787/2000000000 : ℝ)*X 1 2+(2027379209/5000000000 : ℝ)*X 2 0+(4747657061/10000000000 : ℝ)*X 2 1+(685406787/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (917470664926310219517002607/94600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1404974401/100000000000000 : ℝ)*(base19) + (1313056921/100000000000000 : ℝ)*(base23) + (23895249/50000000000000 : ℝ)*(lower2) + (252997919/100000000000000 : ℝ)*(upper3) + (80117511/50000000000000 : ℝ)*(upper5) + (1497068610523883/100000000000000 : ℝ)*(major0) + (1497068610523883/100000000000000 : ℝ)*(major1) + (1497068610523883/100000000000000 : ℝ)*(major2) + (226118238602599/10000000000000 : ℝ)*(sp0) + (113059572844127/5000000000000 : ℝ)*(sp1) + (113059577440001/5000000000000 : ℝ)*(sp2) + (366470114058037/50000000000000 : ℝ)*(sp3) + (1309478869/12500000000000 : ℝ)*(sp4) + (3807794033/100000000000000 : ℝ)*(sp7) + (732944035910107/100000000000000 : ℝ)*(f.failure) + (2261192861856941/100000000000000 : ℝ)*(f.sum) + (74882205278487/47300000000000000000000000000 : ℝ)*base66 + (959193506090877131/189200000000000000000000000000000 : ℝ)*base68 + (1665340681917277131/189200000000000000000000000000000 : ℝ)*base70 + (213737499762322869/189200000000000000000000000000000 : ℝ)*base71 + (5807679840987/47300000000000000000000000000 : ℝ)*base74 + (435140153889922869/189200000000000000000000000000000 : ℝ)*base75 + (836521251053677131/189200000000000000000000000000000 : ℝ)*base78 + (198308629655677131/189200000000000000000000000000000 : ℝ)*base80 + (109118457868587/47300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1633881/200000000000000000000 : ℝ)*base89 + (1633881/200000000000000000000 : ℝ)*base91 + (1633881/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (330202610484552653540067/47300000000000000000000000000 : ℝ) := by norm_num
    linear_combination (940050691/100000000000000 : ℝ)*(base19) + (504674803/50000000000000 : ℝ)*(base23) + (134774733/50000000000000 : ℝ)*(lower1) + (152675803/100000000000000 : ℝ)*(upper3) + (3821403/12500000000000 : ℝ)*(lower4) + (146099127/100000000000000 : ℝ)*(upper5) + (1546645535592633/100000000000000 : ℝ)*(major0) + (1546645535592633/100000000000000 : ℝ)*(major1) + (1546645535592633/100000000000000 : ℝ)*(major2) + (240959881/50000000000000 : ℝ)*(sp2) + (1168037313704867/50000000000000 : ℝ)*(sp4) + (584018421839761/25000000000000 : ℝ)*(sp5) + (1168036568070183/50000000000000 : ℝ)*(sp6) + (378608105537301/50000000000000 : ℝ)*(sp7) + (378608105537301/50000000000000 : ℝ)*(f.failure) + (1168037313704867/50000000000000 : ℝ)*(f.sum) + (223913950596837/47300000000000000000000000000 : ℝ)*base66 + (248729635423345881/189200000000000000000000000000000 : ℝ)*base68 + (283574157063054119/189200000000000000000000000000000 : ℝ)*base69 + (3662587166498545881/189200000000000000000000000000000 : ℝ)*base72 + (73261454253037/47300000000000000000000000000 : ℝ)*base74 + (595173146577745881/189200000000000000000000000000000 : ℝ)*base76 + (272248291637454119/189200000000000000000000000000000 : ℝ)*base77 + (775529039488654119/189200000000000000000000000000000 : ℝ)*base79 + (273575059131237/47300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1180983/100000000000000000000 : ℝ)*base89 + (1180983/100000000000000000000 : ℝ)*base91 + (1180983/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1735_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (731/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1763/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4409/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18271/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1735_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1735_box_0 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-898016671/10000000000 : ℝ)*x 0 + (1360553137/2500000000 : ℝ)*x 1 + (5442207427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898016671/10000000000 : ℝ)^5535 ≤ (2598060534781/50000000000000 : ℝ)^4511 := by
    have hnat : (898016671 : ℕ)^5535*50000000000000^4511 ≤ 2598060534781^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898016671 10000000000 2598060534781 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360553137/2500000000 : ℝ)^5535 ≤ (2962622926319/6250000000000 : ℝ)^4511 := by
    have hnat : (1360553137 : ℕ)^5535*6250000000000^4511 ≤ 2962622926319^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360553137 2500000000 2962622926319 6250000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442207427/10000000000 : ℝ)^5535 ≤ (23700956045871/50000000000000 : ℝ)^4511 := by
    have hnat : (5442207427 : ℕ)^5535*50000000000000^4511 ≤ 23700956045871^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442207427 10000000000 23700956045871 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-898016671/10000000000 : ℝ), (1360553137/2500000000 : ℝ), (5442207427/10000000000 : ℝ)] ![(2598060534781/50000000000000 : ℝ), (2962622926319/6250000000000 : ℝ), (23700956045871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-898016671/10000000000 : ℝ)|^5535 ≤ (2598060534781/50000000000000 : ℝ)^4511
        have hw : |(-898016671/10000000000 : ℝ)|=(898016671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360553137/2500000000 : ℝ)|^5535 ≤ (2962622926319/6250000000000 : ℝ)^4511
        have hw : |(1360553137/2500000000 : ℝ)|=(1360553137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442207427/10000000000 : ℝ)|^5535 ≤ (23700956045871/50000000000000 : ℝ)^4511
        have hw : |(5442207427/10000000000 : ℝ)|=(5442207427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_1 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162355183/312500000 : ℝ)*x 0 + (-626550787/5000000000 : ℝ)*x 1 + (1088443273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162355183/312500000 : ℝ)^5535 ≤ (44777599701699/100000000000000 : ℝ)^4511 := by
    have hnat : (162355183 : ℕ)^5535*100000000000000^4511 ≤ 44777599701699^4511*312500000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162355183 312500000 44777599701699 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626550787/5000000000 : ℝ)^5535 ≤ (7820392673139/100000000000000 : ℝ)^4511 := by
    have hnat : (626550787 : ℕ)^5535*100000000000000^4511 ≤ 7820392673139^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626550787 5000000000 7820392673139 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088443273/2000000000 : ℝ)^5535 ≤ (5925250951789/12500000000000 : ℝ)^4511 := by
    have hnat : (1088443273 : ℕ)^5535*12500000000000^4511 ≤ 5925250951789^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088443273 2000000000 5925250951789 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162355183/312500000 : ℝ), (-626550787/5000000000 : ℝ), (1088443273/2000000000 : ℝ)] ![(44777599701699/100000000000000 : ℝ), (7820392673139/100000000000000 : ℝ), (5925250951789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162355183/312500000 : ℝ)|^5535 ≤ (44777599701699/100000000000000 : ℝ)^4511
        have hw : |(162355183/312500000 : ℝ)|=(162355183/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-626550787/5000000000 : ℝ)|^5535 ≤ (7820392673139/100000000000000 : ℝ)^4511
        have hw : |(-626550787/5000000000 : ℝ)|=(626550787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088443273/2000000000 : ℝ)|^5535 ≤ (5925250951789/12500000000000 : ℝ)^4511
        have hw : |(1088443273/2000000000 : ℝ)|=(1088443273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_2 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259768749/500000000 : ℝ)*x 0 + (1088441779/2000000000 : ℝ)*x 1 + (-626549699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259768749/500000000 : ℝ)^5535 ≤ (44777696190039/100000000000000 : ℝ)^4511 := by
    have hnat : (259768749 : ℕ)^5535*100000000000000^4511 ≤ 44777696190039^4511*500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259768749 500000000 44777696190039 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088441779/2000000000 : ℝ)^5535 ≤ (47401927780611/100000000000000 : ℝ)^4511 := by
    have hnat : (1088441779 : ℕ)^5535*100000000000000^4511 ≤ 47401927780611^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088441779 2000000000 47401927780611 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626549699/5000000000 : ℝ)^5535 ≤ (7820376010419/100000000000000 : ℝ)^4511 := by
    have hnat : (626549699 : ℕ)^5535*100000000000000^4511 ≤ 7820376010419^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626549699 5000000000 7820376010419 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259768749/500000000 : ℝ), (1088441779/2000000000 : ℝ), (-626549699/5000000000 : ℝ)] ![(44777696190039/100000000000000 : ℝ), (47401927780611/100000000000000 : ℝ), (7820376010419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259768749/500000000 : ℝ)|^5535 ≤ (44777696190039/100000000000000 : ℝ)^4511
        have hw : |(259768749/500000000 : ℝ)|=(259768749/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088441779/2000000000 : ℝ)|^5535 ≤ (47401927780611/100000000000000 : ℝ)^4511
        have hw : |(1088441779/2000000000 : ℝ)|=(1088441779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-626549699/5000000000 : ℝ)|^5535 ≤ (7820376010419/100000000000000 : ℝ)^4511
        have hw : |(-626549699/5000000000 : ℝ)|=(626549699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_3 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2291517083/5000000000 : ℝ)*x 0 + (3830191431/10000000000 : ℝ)*x 1 + (3830186729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2291517083/5000000000 : ℝ)^5535 ≤ (19195729722399/50000000000000 : ℝ)^4511 := by
    have hnat : (2291517083 : ℕ)^5535*50000000000000^4511 ≤ 19195729722399^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291517083 5000000000 19195729722399 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3830191431/10000000000 : ℝ)^5535 ≤ (30804293467001/100000000000000 : ℝ)^4511 := by
    have hnat : (3830191431 : ℕ)^5535*100000000000000^4511 ≤ 30804293467001^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3830191431 10000000000 30804293467001 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3830186729/10000000000 : ℝ)^5535 ≤ (6160849413397/20000000000000 : ℝ)^4511 := by
    have hnat : (3830186729 : ℕ)^5535*20000000000000^4511 ≤ 6160849413397^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3830186729 10000000000 6160849413397 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2291517083/5000000000 : ℝ), (3830191431/10000000000 : ℝ), (3830186729/10000000000 : ℝ)] ![(19195729722399/50000000000000 : ℝ), (30804293467001/100000000000000 : ℝ), (6160849413397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2291517083/5000000000 : ℝ)|^5535 ≤ (19195729722399/50000000000000 : ℝ)^4511
        have hw : |(2291517083/5000000000 : ℝ)|=(2291517083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3830191431/10000000000 : ℝ)|^5535 ≤ (30804293467001/100000000000000 : ℝ)^4511
        have hw : |(3830191431/10000000000 : ℝ)|=(3830191431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3830186729/10000000000 : ℝ)|^5535 ≤ (6160849413397/20000000000000 : ℝ)^4511
        have hw : |(3830186729/10000000000 : ℝ)|=(3830186729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_4 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-882642317/5000000000 : ℝ)*x 0 + (512607689/1000000000 : ℝ)*x 1 + (640759637/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882642317/5000000000 : ℝ)^5535 ≤ (11908064714903/100000000000000 : ℝ)^4511 := by
    have hnat : (882642317 : ℕ)^5535*100000000000000^4511 ≤ 11908064714903^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882642317 5000000000 11908064714903 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512607689/1000000000 : ℝ)^5535 ≤ (44045966545507/100000000000000 : ℝ)^4511 := by
    have hnat : (512607689 : ℕ)^5535*100000000000000^4511 ≤ 44045966545507^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512607689 1000000000 44045966545507 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640759637/1250000000 : ℝ)^5535 ≤ (44045968717373/100000000000000 : ℝ)^4511 := by
    have hnat : (640759637 : ℕ)^5535*100000000000000^4511 ≤ 44045968717373^4511*1250000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640759637 1250000000 44045968717373 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882642317/5000000000 : ℝ), (512607689/1000000000 : ℝ), (640759637/1250000000 : ℝ)] ![(11908064714903/100000000000000 : ℝ), (44045966545507/100000000000000 : ℝ), (44045968717373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882642317/5000000000 : ℝ)|^5535 ≤ (11908064714903/100000000000000 : ℝ)^4511
        have hw : |(-882642317/5000000000 : ℝ)|=(882642317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512607689/1000000000 : ℝ)|^5535 ≤ (44045966545507/100000000000000 : ℝ)^4511
        have hw : |(512607689/1000000000 : ℝ)|=(512607689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640759637/1250000000 : ℝ)|^5535 ≤ (44045968717373/100000000000000 : ℝ)^4511
        have hw : |(640759637/1250000000 : ℝ)|=(640759637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_5 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5408387723/10000000000 : ℝ)*x 0 + (-1394075819/10000000000 : ℝ)*x 1 + (1025215357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408387723/10000000000 : ℝ)^5535 ≤ (9408145627333/20000000000000 : ℝ)^4511 := by
    have hnat : (5408387723 : ℕ)^5535*20000000000000^4511 ≤ 9408145627333^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408387723 10000000000 9408145627333 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394075819/10000000000 : ℝ)^5535 ≤ (4456653207047/50000000000000 : ℝ)^4511 := by
    have hnat : (1394075819 : ℕ)^5535*50000000000000^4511 ≤ 4456653207047^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394075819 10000000000 4456653207047 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025215357/2000000000 : ℝ)^5535 ≤ (5505745679811/12500000000000 : ℝ)^4511 := by
    have hnat : (1025215357 : ℕ)^5535*12500000000000^4511 ≤ 5505745679811^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025215357 2000000000 5505745679811 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408387723/10000000000 : ℝ), (-1394075819/10000000000 : ℝ), (1025215357/2000000000 : ℝ)] ![(9408145627333/20000000000000 : ℝ), (4456653207047/50000000000000 : ℝ), (5505745679811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408387723/10000000000 : ℝ)|^5535 ≤ (9408145627333/20000000000000 : ℝ)^4511
        have hw : |(5408387723/10000000000 : ℝ)|=(5408387723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1394075819/10000000000 : ℝ)|^5535 ≤ (4456653207047/50000000000000 : ℝ)^4511
        have hw : |(-1394075819/10000000000 : ℝ)|=(1394075819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025215357/2000000000 : ℝ)|^5535 ≤ (5505745679811/12500000000000 : ℝ)^4511
        have hw : |(1025215357/2000000000 : ℝ)|=(1025215357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_6 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (338024199/625000000 : ℝ)*x 0 + (12815193/25000000 : ℝ)*x 1 + (-278815199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338024199/625000000 : ℝ)^5535 ≤ (11760180596097/25000000000000 : ℝ)^4511 := by
    have hnat : (338024199 : ℕ)^5535*25000000000000^4511 ≤ 11760180596097^4511*625000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338024199 625000000 11760180596097 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12815193/25000000 : ℝ)^5535 ≤ (44045969813849/100000000000000 : ℝ)^4511 := by
    have hnat : (12815193 : ℕ)^5535*100000000000000^4511 ≤ 44045969813849^4511*25000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12815193 25000000 44045969813849 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278815199/2000000000 : ℝ)^5535 ≤ (2228326948707/25000000000000 : ℝ)^4511 := by
    have hnat : (278815199 : ℕ)^5535*25000000000000^4511 ≤ 2228326948707^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278815199 2000000000 2228326948707 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338024199/625000000 : ℝ), (12815193/25000000 : ℝ), (-278815199/2000000000 : ℝ)] ![(11760180596097/25000000000000 : ℝ), (44045969813849/100000000000000 : ℝ), (2228326948707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338024199/625000000 : ℝ)|^5535 ≤ (11760180596097/25000000000000 : ℝ)^4511
        have hw : |(338024199/625000000 : ℝ)|=(338024199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12815193/25000000 : ℝ)|^5535 ≤ (44045969813849/100000000000000 : ℝ)^4511
        have hw : |(12815193/25000000 : ℝ)|=(12815193/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278815199/2000000000 : ℝ)|^5535 ≤ (2228326948707/25000000000000 : ℝ)^4511
        have hw : |(-278815199/2000000000 : ℝ)|=(278815199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_7 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1745104063/5000000000 : ℝ)*x 0 + (68349711/156250000 : ℝ)*x 1 + (218719057/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1745104063/5000000000 : ℝ)^5535 ≤ (27483894459531/100000000000000 : ℝ)^4511 := by
    have hnat : (1745104063 : ℕ)^5535*100000000000000^4511 ≤ 27483894459531^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745104063 5000000000 27483894459531 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68349711/156250000 : ℝ)^5535 ≤ (36258054616581/100000000000000 : ℝ)^4511 := by
    have hnat : (68349711 : ℕ)^5535*100000000000000^4511 ≤ 36258054616581^4511*156250000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68349711 156250000 36258054616581 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218719057/500000000 : ℝ)^5535 ≤ (18129025457301/50000000000000 : ℝ)^4511 := by
    have hnat : (218719057 : ℕ)^5535*50000000000000^4511 ≤ 18129025457301^4511*500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218719057 500000000 18129025457301 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1745104063/5000000000 : ℝ), (68349711/156250000 : ℝ), (218719057/500000000 : ℝ)] ![(27483894459531/100000000000000 : ℝ), (36258054616581/100000000000000 : ℝ), (18129025457301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1745104063/5000000000 : ℝ)|^5535 ≤ (27483894459531/100000000000000 : ℝ)^4511
        have hw : |(1745104063/5000000000 : ℝ)|=(1745104063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68349711/156250000 : ℝ)|^5535 ≤ (36258054616581/100000000000000 : ℝ)^4511
        have hw : |(68349711/156250000 : ℝ)|=(68349711/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218719057/500000000 : ℝ)|^5535 ≤ (18129025457301/50000000000000 : ℝ)^4511
        have hw : |(218719057/500000000 : ℝ)|=(218719057/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_8 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1577223919/10000000000 : ℝ)*x 0 + (4887066263/10000000000 : ℝ)*x 1 + (2753233001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1577223919/10000000000 : ℝ)^5535 ≤ (40511157053/390625000000 : ℝ)^4511 := by
    have hnat : (1577223919 : ℕ)^5535*390625000000^4511 ≤ 40511157053^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577223919 10000000000 40511157053 390625000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4887066263/10000000000 : ℝ)^5535 ≤ (5192445913817/12500000000000 : ℝ)^4511 := by
    have hnat : (4887066263 : ℕ)^5535*12500000000000^4511 ≤ 5192445913817^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4887066263 10000000000 5192445913817 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2753233001/5000000000 : ℝ)^5535 ≤ (48089576471471/100000000000000 : ℝ)^4511 := by
    have hnat : (2753233001 : ℕ)^5535*100000000000000^4511 ≤ 48089576471471^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753233001 5000000000 48089576471471 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1577223919/10000000000 : ℝ), (4887066263/10000000000 : ℝ), (2753233001/5000000000 : ℝ)] ![(40511157053/390625000000 : ℝ), (5192445913817/12500000000000 : ℝ), (48089576471471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1577223919/10000000000 : ℝ)|^5535 ≤ (40511157053/390625000000 : ℝ)^4511
        have hw : |(-1577223919/10000000000 : ℝ)|=(1577223919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4887066263/10000000000 : ℝ)|^5535 ≤ (5192445913817/12500000000000 : ℝ)^4511
        have hw : |(4887066263/10000000000 : ℝ)|=(4887066263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2753233001/5000000000 : ℝ)|^5535 ≤ (48089576471471/100000000000000 : ℝ)^4511
        have hw : |(2753233001/5000000000 : ℝ)|=(2753233001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_9 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576063651/5000000000 : ℝ)*x 0 + (-1222885141/10000000000 : ℝ)*x 1 + (1376616517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576063651/5000000000 : ℝ)^5535 ≤ (11080193818911/25000000000000 : ℝ)^4511 := by
    have hnat : (2576063651 : ℕ)^5535*25000000000000^4511 ≤ 11080193818911^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576063651 5000000000 11080193818911 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1222885141/10000000000 : ℝ)^5535 ≤ (7589647536787/100000000000000 : ℝ)^4511 := by
    have hnat : (1222885141 : ℕ)^5535*100000000000000^4511 ≤ 7589647536787^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222885141 10000000000 7589647536787 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376616517/2500000000 : ℝ)^5535 ≤ (48089577178711/100000000000000 : ℝ)^4511 := by
    have hnat : (1376616517 : ℕ)^5535*100000000000000^4511 ≤ 48089577178711^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376616517 2500000000 48089577178711 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576063651/5000000000 : ℝ), (-1222885141/10000000000 : ℝ), (1376616517/2500000000 : ℝ)] ![(11080193818911/25000000000000 : ℝ), (7589647536787/100000000000000 : ℝ), (48089577178711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576063651/5000000000 : ℝ)|^5535 ≤ (11080193818911/25000000000000 : ℝ)^4511
        have hw : |(2576063651/5000000000 : ℝ)|=(2576063651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1222885141/10000000000 : ℝ)|^5535 ≤ (7589647536787/100000000000000 : ℝ)^4511
        have hw : |(-1222885141/10000000000 : ℝ)|=(1222885141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376616517/2500000000 : ℝ)|^5535 ≤ (48089577178711/100000000000000 : ℝ)^4511
        have hw : |(1376616517/2500000000 : ℝ)|=(1376616517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_10 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152127129/10000000000 : ℝ)*x 0 + (68830827/125000000 : ℝ)*x 1 + (-1222885251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152127129/10000000000 : ℝ)^5535 ≤ (44320773449599/100000000000000 : ℝ)^4511 := by
    have hnat : (5152127129 : ℕ)^5535*100000000000000^4511 ≤ 44320773449599^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152127129 10000000000 44320773449599 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68830827/125000000 : ℝ)^5535 ≤ (48089578164561/100000000000000 : ℝ)^4511 := by
    have hnat : (68830827 : ℕ)^5535*100000000000000^4511 ≤ 48089578164561^4511*125000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68830827 125000000 48089578164561 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1222885251/10000000000 : ℝ)^5535 ≤ (7589648374457/100000000000000 : ℝ)^4511 := by
    have hnat : (1222885251 : ℕ)^5535*100000000000000^4511 ≤ 7589648374457^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222885251 10000000000 7589648374457 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152127129/10000000000 : ℝ), (68830827/125000000 : ℝ), (-1222885251/10000000000 : ℝ)] ![(44320773449599/100000000000000 : ℝ), (48089578164561/100000000000000 : ℝ), (7589648374457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152127129/10000000000 : ℝ)|^5535 ≤ (44320773449599/100000000000000 : ℝ)^4511
        have hw : |(5152127129/10000000000 : ℝ)|=(5152127129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68830827/125000000 : ℝ)|^5535 ≤ (48089578164561/100000000000000 : ℝ)^4511
        have hw : |(68830827/125000000 : ℝ)|=(68830827/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1222885251/10000000000 : ℝ)|^5535 ≤ (7589648374457/100000000000000 : ℝ)^4511
        have hw : |(-1222885251/10000000000 : ℝ)|=(1222885251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_11 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4794422359/10000000000 : ℝ)*x 0 + (464895353/1250000000 : ℝ)*x 1 + (3719163233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4794422359/10000000000 : ℝ)^5535 ≤ (10143859475607/25000000000000 : ℝ)^4511 := by
    have hnat : (4794422359 : ℕ)^5535*25000000000000^4511 ≤ 10143859475607^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794422359 10000000000 10143859475607 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464895353/1250000000 : ℝ)^5535 ≤ (29712279037071/100000000000000 : ℝ)^4511 := by
    have hnat : (464895353 : ℕ)^5535*100000000000000^4511 ≤ 29712279037071^4511*1250000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464895353 1250000000 29712279037071 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3719163233/10000000000 : ℝ)^5535 ≤ (14856141523141/50000000000000 : ℝ)^4511 := by
    have hnat : (3719163233 : ℕ)^5535*50000000000000^4511 ≤ 14856141523141^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3719163233 10000000000 14856141523141 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4794422359/10000000000 : ℝ), (464895353/1250000000 : ℝ), (3719163233/10000000000 : ℝ)] ![(10143859475607/25000000000000 : ℝ), (29712279037071/100000000000000 : ℝ), (14856141523141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4794422359/10000000000 : ℝ)|^5535 ≤ (10143859475607/25000000000000 : ℝ)^4511
        have hw : |(4794422359/10000000000 : ℝ)|=(4794422359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(464895353/1250000000 : ℝ)|^5535 ≤ (29712279037071/100000000000000 : ℝ)^4511
        have hw : |(464895353/1250000000 : ℝ)|=(464895353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3719163233/10000000000 : ℝ)|^5535 ≤ (14856141523141/50000000000000 : ℝ)^4511
        have hw : |(3719163233/10000000000 : ℝ)|=(3719163233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_12 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073416523/10000000000 : ℝ)*x 0 + (566636333/1000000000 : ℝ)*x 1 + (5095486081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073416523/10000000000 : ℝ)^5535 ≤ (6467732210983/100000000000000 : ℝ)^4511 := by
    have hnat : (1073416523 : ℕ)^5535*100000000000000^4511 ≤ 6467732210983^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073416523 10000000000 6467732210983 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566636333/1000000000 : ℝ)^5535 ≤ (1556518829577/3125000000000 : ℝ)^4511 := by
    have hnat : (566636333 : ℕ)^5535*3125000000000^4511 ≤ 1556518829577^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566636333 1000000000 1556518829577 3125000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5095486081/10000000000 : ℝ)^5535 ≤ (8744733046773/20000000000000 : ℝ)^4511 := by
    have hnat : (5095486081 : ℕ)^5535*20000000000000^4511 ≤ 8744733046773^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095486081 10000000000 8744733046773 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073416523/10000000000 : ℝ), (566636333/1000000000 : ℝ), (5095486081/10000000000 : ℝ)] ![(6467732210983/100000000000000 : ℝ), (1556518829577/3125000000000 : ℝ), (8744733046773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073416523/10000000000 : ℝ)|^5535 ≤ (6467732210983/100000000000000 : ℝ)^4511
        have hw : |(-1073416523/10000000000 : ℝ)|=(1073416523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566636333/1000000000 : ℝ)|^5535 ≤ (1556518829577/3125000000000 : ℝ)^4511
        have hw : |(566636333/1000000000 : ℝ)|=(566636333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5095486081/10000000000 : ℝ)|^5535 ≤ (8744733046773/20000000000000 : ℝ)^4511
        have hw : |(5095486081/10000000000 : ℝ)|=(5095486081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_13 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542906853/1000000000 : ℝ)*x 0 + (-281399991/2000000000 : ℝ)*x 1 + (5095485987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542906853/1000000000 : ℝ)^5535 ≤ (47261532045671/100000000000000 : ℝ)^4511 := by
    have hnat : (542906853 : ℕ)^5535*100000000000000^4511 ≤ 47261532045671^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542906853 1000000000 47261532045671 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281399991/2000000000 : ℝ)^5535 ≤ (2253700924059/25000000000000 : ℝ)^4511 := by
    have hnat : (281399991 : ℕ)^5535*25000000000000^4511 ≤ 2253700924059^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281399991 2000000000 2253700924059 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5095485987/10000000000 : ℝ)^5535 ≤ (8744732848833/20000000000000 : ℝ)^4511 := by
    have hnat : (5095485987 : ℕ)^5535*20000000000000^4511 ≤ 8744732848833^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095485987 10000000000 8744732848833 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542906853/1000000000 : ℝ), (-281399991/2000000000 : ℝ), (5095485987/10000000000 : ℝ)] ![(47261532045671/100000000000000 : ℝ), (2253700924059/25000000000000 : ℝ), (8744732848833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542906853/1000000000 : ℝ)|^5535 ≤ (47261532045671/100000000000000 : ℝ)^4511
        have hw : |(542906853/1000000000 : ℝ)|=(542906853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-281399991/2000000000 : ℝ)|^5535 ≤ (2253700924059/25000000000000 : ℝ)^4511
        have hw : |(-281399991/2000000000 : ℝ)|=(281399991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5095485987/10000000000 : ℝ)|^5535 ≤ (8744732848833/20000000000000 : ℝ)^4511
        have hw : |(5095485987/10000000000 : ℝ)|=(5095485987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_14 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2714534409/5000000000 : ℝ)*x 0 + (5095485809/10000000000 : ℝ)*x 1 + (-1406999803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2714534409/5000000000 : ℝ)^5535 ≤ (11815383780477/25000000000000 : ℝ)^4511 := by
    have hnat : (2714534409 : ℕ)^5535*25000000000000^4511 ≤ 11815383780477^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714534409 5000000000 11815383780477 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5095485809/10000000000 : ℝ)^5535 ≤ (10930915592513/25000000000000 : ℝ)^4511 := by
    have hnat : (5095485809 : ℕ)^5535*25000000000000^4511 ≤ 10930915592513^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095485809 10000000000 10930915592513 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1406999803/10000000000 : ℝ)^5535 ≤ (9014802501283/100000000000000 : ℝ)^4511 := by
    have hnat : (1406999803 : ℕ)^5535*100000000000000^4511 ≤ 9014802501283^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406999803 10000000000 9014802501283 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2714534409/5000000000 : ℝ), (5095485809/10000000000 : ℝ), (-1406999803/10000000000 : ℝ)] ![(11815383780477/25000000000000 : ℝ), (10930915592513/25000000000000 : ℝ), (9014802501283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2714534409/5000000000 : ℝ)|^5535 ≤ (11815383780477/25000000000000 : ℝ)^4511
        have hw : |(2714534409/5000000000 : ℝ)|=(2714534409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5095485809/10000000000 : ℝ)|^5535 ≤ (10930915592513/25000000000000 : ℝ)^4511
        have hw : |(5095485809/10000000000 : ℝ)|=(5095485809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1406999803/10000000000 : ℝ)|^5535 ≤ (9014802501283/100000000000000 : ℝ)^4511
        have hw : |(-1406999803/10000000000 : ℝ)|=(1406999803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_box_15 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675847597/2000000000 : ℝ)*x 0 + (2213415501/5000000000 : ℝ)*x 1 + (4426831109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675847597/2000000000 : ℝ)^5535 ≤ (6603897688797/25000000000000 : ℝ)^4511 := by
    have hnat : (675847597 : ℕ)^5535*25000000000000^4511 ≤ 6603897688797^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675847597 2000000000 6603897688797 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213415501/5000000000 : ℝ)^5535 ≤ (9198051016771/25000000000000 : ℝ)^4511 := by
    have hnat : (2213415501 : ℕ)^5535*25000000000000^4511 ≤ 9198051016771^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213415501 5000000000 9198051016771 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426831109/10000000000 : ℝ)^5535 ≤ (9198051289563/25000000000000 : ℝ)^4511 := by
    have hnat : (4426831109 : ℕ)^5535*25000000000000^4511 ≤ 9198051289563^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426831109 10000000000 9198051289563 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675847597/2000000000 : ℝ), (2213415501/5000000000 : ℝ), (4426831109/10000000000 : ℝ)] ![(6603897688797/25000000000000 : ℝ), (9198051016771/25000000000000 : ℝ), (9198051289563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675847597/2000000000 : ℝ)|^5535 ≤ (6603897688797/25000000000000 : ℝ)^4511
        have hw : |(675847597/2000000000 : ℝ)|=(675847597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213415501/5000000000 : ℝ)|^5535 ≤ (9198051016771/25000000000000 : ℝ)^4511
        have hw : |(2213415501/5000000000 : ℝ)|=(2213415501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426831109/10000000000 : ℝ)|^5535 ≤ (9198051289563/25000000000000 : ℝ)^4511
        have hw : |(4426831109/10000000000 : ℝ)|=(4426831109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1735_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(8581/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57357/100000 : ℝ) ∧ (80647/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (23153/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4409/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4409/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4409/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4409/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4409/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4409/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4409/50000 : ℝ) ^ (5519/1024 : ℝ) ≤ (206973897375937/100000000000000000000 : ℝ) := by
    have hpowers : (4409/50000 : ℝ)^5519 ≤ (206973897375937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4409 : ℕ)^5519*100000000000000000000^1024 ≤ 206973897375937^1024*50000^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4409 50000 206973897375937 100000000000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4409/50000 : ℝ)) (X := (206973897375937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18271/100000 : ℝ) ^ (5519/1024 : ℝ) ≤ (16405083854329/156250000000000000 : ℝ) := by
    have hpowers : (18271/100000 : ℝ)^5519 ≤ (16405083854329/156250000000000000 : ℝ)^1024 := by
      have hnat : (18271 : ℕ)^5519*156250000000000000^1024 ≤ 16405083854329^1024*100000^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18271 100000 16405083854329 156250000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18271/100000 : ℝ)) (X := (16405083854329/156250000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000206973897375937/50000000000000000000 : ℝ) ≤ (10000007680409989/10000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (50000206973897375937/50000000000000000000 : ℝ)^1024 ≤ (10000007680409989/10000000000000000 : ℝ)^5519 := by
      have hnat : (50000206973897375937 : ℕ)^1024*10000000000000000^5519 ≤ 10000007680409989^5519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000206973897375937 50000000000000000000 10000007680409989 10000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000007680409989/10000000000000000 : ℝ)) (X := (50000206973897375937/50000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010706227564146497/100000000000000000000 : ℝ) ≤ (625012414725351/625000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (100010706227564146497/100000000000000000000 : ℝ)^1024 ≤ (625012414725351/625000000000000 : ℝ)^5519 := by
      have hnat : (100010706227564146497 : ℕ)^1024*625000000000000^5519 ≤ 625012414725351^5519*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010706227564146497 100000000000000000000 625012414725351 625000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625012414725351/625000000000000 : ℝ)) (X := (100010706227564146497/100000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (78141405083854329/78125000000000000 : ℝ) ≤ (10000389590801243/10000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (78141405083854329/78125000000000000 : ℝ)^1024 ≤ (10000389590801243/10000000000000000 : ℝ)^5519 := by
      have hnat : (78141405083854329 : ℕ)^1024*10000000000000000^5519 ≤ 10000389590801243^5519*78125000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78141405083854329 78125000000000000 10000389590801243 10000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000389590801243/10000000000000000 : ℝ)) (X := (78141405083854329/78125000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(206973897375937/100000000000000000000 : ℝ) ≤ ((18905340983417109649/18906000000000000000 : ℝ)+2*(190955195627/945300000000000 : ℝ)*(4409/50000 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (18905340983417109649/18906000000000000000 : ℝ)+2*(190955195627/945300000000000 : ℝ)*(4409/50000 : ℝ)=(10000007680409989/10000000000000000 : ℝ) by norm_num, show 1+2*(206973897375937/100000000000000000000 : ℝ)=(50000206973897375937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16405083854329/156250000000000000 : ℝ)+(206973897375937/100000000000000000000 : ℝ) ≤ ((18905340983417109649/18906000000000000000 : ℝ)+(190955195627/945300000000000 : ℝ)*((18271/100000 : ℝ)+(4409/50000 : ℝ)))^(5519/1024 : ℝ) := by
    rw [show (18905340983417109649/18906000000000000000 : ℝ)+(190955195627/945300000000000 : ℝ)*((18271/100000 : ℝ)+(4409/50000 : ℝ))=(625012414725351/625000000000000 : ℝ) by norm_num, show 1+(16405083854329/156250000000000000 : ℝ)+(206973897375937/100000000000000000000 : ℝ)=(100010706227564146497/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16405083854329/156250000000000000 : ℝ) ≤ ((18905340983417109649/18906000000000000000 : ℝ)+2*(190955195627/945300000000000 : ℝ)*(18271/100000 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (18905340983417109649/18906000000000000000 : ℝ)+2*(190955195627/945300000000000 : ℝ)*(18271/100000 : ℝ)=(10000389590801243/10000000000000000 : ℝ) by norm_num, show 1+2*(16405083854329/156250000000000000 : ℝ)=(78141405083854329/78125000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18905340983417109649/18906000000000000000 : ℝ)*(X 1 0+X 2 0)+(190955195627/945300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (4409/50000 : ℝ)) (hi := (18271/100000 : ℝ)) (c := (18905340983417109649/18906000000000000000 : ℝ)) (alpha := (190955195627/945300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18905340983417109649/18906000000000000000 : ℝ)*(X 0 1+X 2 1)+(190955195627/945300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (4409/50000 : ℝ)) (hi := (18271/100000 : ℝ)) (c := (18905340983417109649/18906000000000000000 : ℝ)) (alpha := (190955195627/945300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18905340983417109649/18906000000000000000 : ℝ)*(X 0 2+X 1 2)+(190955195627/945300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (4409/50000 : ℝ)) (hi := (18271/100000 : ℝ)) (c := (18905340983417109649/18906000000000000000 : ℝ)) (alpha := (190955195627/945300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-898016671/10000000000 : ℝ)*X 0 0+(1360553137/2500000000 : ℝ)*X 0 1+(5442207427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((162355183/312500000 : ℝ)*X 1 0+(-626550787/5000000000 : ℝ)*X 1 1+(1088443273/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((259768749/500000000 : ℝ)*X 2 0+(1088441779/2000000000 : ℝ)*X 2 1+(-626549699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2291517083/5000000000 : ℝ)*X 0 0+(3830191431/10000000000 : ℝ)*X 0 1+(3830186729/10000000000 : ℝ)*X 0 2+(2291517083/5000000000 : ℝ)*X 1 0+(3830191431/10000000000 : ℝ)*X 1 1+(3830186729/10000000000 : ℝ)*X 1 2+(2291517083/5000000000 : ℝ)*X 2 0+(3830191431/10000000000 : ℝ)*X 2 1+(3830186729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-882642317/5000000000 : ℝ)*X 0 0+(512607689/1000000000 : ℝ)*X 0 1+(640759637/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5408387723/10000000000 : ℝ)*X 1 0+(-1394075819/10000000000 : ℝ)*X 1 1+(1025215357/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((338024199/625000000 : ℝ)*X 2 0+(12815193/25000000 : ℝ)*X 2 1+(-278815199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1745104063/5000000000 : ℝ)*X 0 0+(68349711/156250000 : ℝ)*X 0 1+(218719057/500000000 : ℝ)*X 0 2+(1745104063/5000000000 : ℝ)*X 1 0+(68349711/156250000 : ℝ)*X 1 1+(218719057/500000000 : ℝ)*X 1 2+(1745104063/5000000000 : ℝ)*X 2 0+(68349711/156250000 : ℝ)*X 2 1+(218719057/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1577223919/10000000000 : ℝ)*X 0 0+(4887066263/10000000000 : ℝ)*X 0 1+(2753233001/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576063651/5000000000 : ℝ)*X 1 0+(-1222885141/10000000000 : ℝ)*X 1 1+(1376616517/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152127129/10000000000 : ℝ)*X 2 0+(68830827/125000000 : ℝ)*X 2 1+(-1222885251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4794422359/10000000000 : ℝ)*X 0 0+(464895353/1250000000 : ℝ)*X 0 1+(3719163233/10000000000 : ℝ)*X 0 2+(4794422359/10000000000 : ℝ)*X 1 0+(464895353/1250000000 : ℝ)*X 1 1+(3719163233/10000000000 : ℝ)*X 1 2+(4794422359/10000000000 : ℝ)*X 2 0+(464895353/1250000000 : ℝ)*X 2 1+(3719163233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1073416523/10000000000 : ℝ)*X 0 0+(566636333/1000000000 : ℝ)*X 0 1+(5095486081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((542906853/1000000000 : ℝ)*X 1 0+(-281399991/2000000000 : ℝ)*X 1 1+(5095485987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2714534409/5000000000 : ℝ)*X 2 0+(5095485809/10000000000 : ℝ)*X 2 1+(-1406999803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((675847597/2000000000 : ℝ)*X 0 0+(2213415501/5000000000 : ℝ)*X 0 1+(4426831109/10000000000 : ℝ)*X 0 2+(675847597/2000000000 : ℝ)*X 1 0+(2213415501/5000000000 : ℝ)*X 1 1+(4426831109/10000000000 : ℝ)*X 1 2+(675847597/2000000000 : ℝ)*X 2 0+(2213415501/5000000000 : ℝ)*X 2 1+(4426831109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-8581/12500 : ℝ) ≤ (-108151397735663615825415203861211/157550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8404577/12500000000000 : ℝ)*(upper1) + (682769/4000000000000 : ℝ)*(upper2) + (3929627/20000000000000 : ℝ)*(upper3) + (59242761/100000000000000 : ℝ)*(lower4) + (1915859/5000000000000 : ℝ)*(upper5) + (498967315433287/50000000000000 : ℝ)*(major0) + (498967315433287/50000000000000 : ℝ)*(major1) + (498967315433287/50000000000000 : ℝ)*(major2) + (415226283/100000000000000 : ℝ)*(sp3) + (765088111363091/50000000000000 : ℝ)*(sp4) + (765088111363091/50000000000000 : ℝ)*(sp5) + (7650866210283/500000000000 : ℝ)*(sp6) + (61071818048107/12500000000000 : ℝ)*(sp7) + (2980669583/100000000000000 : ℝ)*(sp14) + (488574959611139/100000000000000 : ℝ)*(f.failure) + (765088111363091/50000000000000 : ℝ)*(f.sum) + (601298403323/11816250000000000000000000000 : ℝ)*base66 + (6714254987435633737/945300000000000000000000000000000 : ℝ)*base68 + (7526573248098233737/945300000000000000000000000000000 : ℝ)*base70 + (7479730609083533737/945300000000000000000000000000000 : ℝ)*base72 + (31409544865937/47265000000000000000000000000 : ℝ)*base74 + (11999881636427633737/945300000000000000000000000000000 : ℝ)*base76 + (6297645917255933737/945300000000000000000000000000000 : ℝ)*base78 + (11928372552850733737/945300000000000000000000000000000 : ℝ)*base80 + (72297193489643/11816250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2539537/200000000000000000000 : ℝ)*base89 + (2539537/200000000000000000000 : ℝ)*base91 + (2539537/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57357/100000 : ℝ) ≤ (22592420403182295912906818957847/39387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62106419/20000000000000 : ℝ)*(lower1) + (6332549/10000000000000 : ℝ)*(lower2) + (1142501261/100000000000000 : ℝ)*(upper4) + (278150124138897/25000000000000 : ℝ)*(major0) + (278150124138897/25000000000000 : ℝ)*(major1) + (278150124138897/25000000000000 : ℝ)*(major2) + (1661346095883837/100000000000000 : ℝ)*(sp0) + (1661334614258403/100000000000000 : ℝ)*(sp1) + (207668645769521/12500000000000 : ℝ)*(sp2) + (272353458464799/50000000000000 : ℝ)*(sp3) + (8203098407/25000000000000 : ℝ)*(sp5) + (18260495863/100000000000000 : ℝ)*(sp6) + (54886091/800000000000 : ℝ)*(sp7) + (21330768193/100000000000000 : ℝ)*(sp8) + (272356888845487/50000000000000 : ℝ)*(f.failure) + (166136742665203/10000000000000 : ℝ)*(f.sum) + (8429876527159/1969375000000000000000000000 : ℝ)*base65 + (1459083516584949051/157550000000000000000000000000000 : ℝ)*base67 + (1046718124977249051/157550000000000000000000000000000 : ℝ)*base69 + (1626960390189599051/157550000000000000000000000000000 : ℝ)*base71 + (200176605037/61542968750000000000000000 : ℝ)*base73 + (19888961162250949/157550000000000000000000000000000 : ℝ)*base76 + (160456722568599051/157550000000000000000000000000000 : ℝ)*base77 + (559192809971199051/157550000000000000000000000000000 : ℝ)*base79 + (24044174888677/15755000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (570421/100000000000000000000 : ℝ)*base89 + (570421/100000000000000000000 : ℝ)*base91 + (570421/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80647/100000 : ℝ) ≤ (254125361361858976377579181151147/315100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15924873/50000000000000 : ℝ)*(upper2) + (2440531/25000000000000 : ℝ)*(lower3) + (4320243/100000000000000 : ℝ)*(lower4) + (1086688566202601/100000000000000 : ℝ)*(major0) + (1086688566202601/100000000000000 : ℝ)*(major1) + (1086688566202601/100000000000000 : ℝ)*(major2) + (2849848281/50000000000000 : ℝ)*(sp1) + (3793239151/100000000000000 : ℝ)*(sp2) + (69721009/20000000000000 : ℝ)*(sp3) + (425952991/100000000000000 : ℝ)*(sp4) + (201808251534797/12500000000000 : ℝ)*(sp8) + (322892147706961/20000000000000 : ℝ)*(sp9) + (201807830624027/12500000000000 : ℝ)*(sp10) + (26601365361789/5000000000000 : ℝ)*(sp11) + (66503456980103/12500000000000 : ℝ)*(f.failure) + (1614466438231367/100000000000000 : ℝ)*(f.sum) + (668729747430953/47265000000000000000000000000 : ℝ)*base66 + (11837311480483262951/1890600000000000000000000000000000 : ℝ)*base68 + (1260108615547262951/1890600000000000000000000000000000 : ℝ)*base70 + (19421995375800662951/1890600000000000000000000000000000 : ℝ)*base72 + (71826413429003/47265000000000000000000000000 : ℝ)*base74 + (12374127351716462951/1890600000000000000000000000000000 : ℝ)*base76 + (19830623348977862951/1890600000000000000000000000000000 : ℝ)*base78 + (13342894244609462951/1890600000000000000000000000000000 : ℝ)*base80 + (37761786688153/11816250000000000000000000000 : ℝ)*base81 + (146451/25000000000000000000 : ℝ)*base90 + (146451/25000000000000000000 : ℝ)*base92 + (146451/25000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-23153/25000 : ℝ) ≤ (-58362458836871348257737267118557/63020000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2935459/12500000000000 : ℝ)*(upper1) + (9964307/50000000000000 : ℝ)*(lower2) + (5827/160000000000 : ℝ)*(upper3) + (78791003/100000000000000 : ℝ)*(upper5) + (227860708739631/20000000000000 : ℝ)*(major0) + (227860708739631/20000000000000 : ℝ)*(major1) + (227860708739631/20000000000000 : ℝ)*(major2) + (1103563991/100000000000000 : ℝ)*(sp4) + (7378538977/50000000000000 : ℝ)*(sp6) + (1671737753/25000000000000 : ℝ)*(sp7) + (437922143097617/25000000000000 : ℝ)*(sp12) + (1751689675954459/100000000000000 : ℝ)*(sp13) + (350334983775301/20000000000000 : ℝ)*(sp14) + (139445133100503/25000000000000 : ℝ)*(sp15) + (8715425302391/1562500000000 : ℝ)*(f.failure) + (1751689675954459/100000000000000 : ℝ)*(f.sum) + (1223114859499/630200000000000000000000000 : ℝ)*base66 + (164058620698433173/126040000000000000000000000000000 : ℝ)*base67 + (298749183257233173/126040000000000000000000000000000 : ℝ)*base69 + (426264661694433173/126040000000000000000000000000000 : ℝ)*base71 + (6713540250449/1575500000000000000000000000 : ℝ)*base74 + (568709219043673173/126040000000000000000000000000000 : ℝ)*base75 + (234584623344193173/126040000000000000000000000000000 : ℝ)*base77 + (560446869011833173/126040000000000000000000000000000 : ℝ)*base79 + (65644764907/1575500000000000000000000000 : ℝ)*base82 + (10297/3125000000000000000 : ℝ)*base90 + (10297/3125000000000000000 : ℝ)*base92 + (10297/3125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1735_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8581/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(57357/100000 : ℝ) else (80647/100000 : ℝ) ≤ X j i ∧ X j i ≤ (23153/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1735_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1735_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (731/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1763/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8581/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(57357/100000 : ℝ) else (80647/100000 : ℝ) ≤ X j i ∧ X j i ≤ (23153/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1735_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1735_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (731/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1763/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8581/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(57357/100000 : ℝ) else (80647/100000 : ℝ) ≤ X j i ∧ X j i ≤ (23153/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1735_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
