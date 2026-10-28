-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1256_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:29:30.218445+00:00
-- url     : https://prove2.me/submissions/85be1686-e339-4fb3-958c-7cb136277bf1

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
theorem support_rectangle_w1256_s6_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056758957/5000000000 : ℝ)*x 0 + (2695556431/5000000000 : ℝ)*x 1 + (2633616233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056758957/5000000000 : ℝ)^8449 ≤ (6427048550507/50000000000000 : ℝ)^6401 := by
    have hnat : (1056758957 : ℕ)^8449*50000000000000^6401 ≤ 6427048550507^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056758957 5000000000 6427048550507 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695556431/5000000000 : ℝ)^8449 ≤ (44241407316951/100000000000000 : ℝ)^6401 := by
    have hnat : (2695556431 : ℕ)^8449*100000000000000^6401 ≤ 44241407316951^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695556431 5000000000 44241407316951 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633616233/5000000000 : ℝ)^8449 ≤ (1340765486647/3125000000000 : ℝ)^6401 := by
    have hnat : (2633616233 : ℕ)^8449*3125000000000^6401 ≤ 1340765486647^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633616233 5000000000 1340765486647 3125000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056758957/5000000000 : ℝ), (2695556431/5000000000 : ℝ), (2633616233/5000000000 : ℝ)] ![(6427048550507/50000000000000 : ℝ), (44241407316951/100000000000000 : ℝ), (1340765486647/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056758957/5000000000 : ℝ)|^8449 ≤ (6427048550507/50000000000000 : ℝ)^6401
        have hw : |(-1056758957/5000000000 : ℝ)|=(1056758957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695556431/5000000000 : ℝ)|^8449 ≤ (44241407316951/100000000000000 : ℝ)^6401
        have hw : |(2695556431/5000000000 : ℝ)|=(2695556431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633616233/5000000000 : ℝ)|^8449 ≤ (1340765486647/3125000000000 : ℝ)^6401
        have hw : |(2633616233/5000000000 : ℝ)|=(2633616233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s6_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534427863/1000000000 : ℝ)*x 0 + (-435265531/2000000000 : ℝ)*x 1 + (5267232461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534427863/1000000000 : ℝ)^8449 ≤ (5466850763809/12500000000000 : ℝ)^6401 := by
    have hnat : (534427863 : ℕ)^8449*12500000000000^6401 ≤ 5466850763809^6401*1000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534427863 1000000000 5466850763809 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435265531/2000000000 : ℝ)^8449 ≤ (3340174590169/25000000000000 : ℝ)^6401 := by
    have hnat : (435265531 : ℕ)^8449*25000000000000^6401 ≤ 3340174590169^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435265531 2000000000 3340174590169 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267232461/10000000000 : ℝ)^8449 ≤ (21452247759473/50000000000000 : ℝ)^6401 := by
    have hnat : (5267232461 : ℕ)^8449*50000000000000^6401 ≤ 21452247759473^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267232461 10000000000 21452247759473 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534427863/1000000000 : ℝ), (-435265531/2000000000 : ℝ), (5267232461/10000000000 : ℝ)] ![(5466850763809/12500000000000 : ℝ), (3340174590169/25000000000000 : ℝ), (21452247759473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534427863/1000000000 : ℝ)|^8449 ≤ (5466850763809/12500000000000 : ℝ)^6401
        have hw : |(534427863/1000000000 : ℝ)|=(534427863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435265531/2000000000 : ℝ)|^8449 ≤ (3340174590169/25000000000000 : ℝ)^6401
        have hw : |(-435265531/2000000000 : ℝ)|=(435265531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267232461/10000000000 : ℝ)|^8449 ≤ (21452247759473/50000000000000 : ℝ)^6401
        have hw : |(5267232461/10000000000 : ℝ)|=(5267232461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s6_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344278637/10000000000 : ℝ)*x 0 + (263361623/500000000 : ℝ)*x 1 + (-2176327647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344278637/10000000000 : ℝ)^8449 ≤ (10933701546521/25000000000000 : ℝ)^6401 := by
    have hnat : (5344278637 : ℕ)^8449*25000000000000^6401 ≤ 10933701546521^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344278637 10000000000 10933701546521 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263361623/500000000 : ℝ)^8449 ≤ (21452247754097/50000000000000 : ℝ)^6401 := by
    have hnat : (263361623 : ℕ)^8449*50000000000000^6401 ≤ 21452247754097^6401*500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263361623 500000000 21452247754097 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176327647/10000000000 : ℝ)^8449 ≤ (267213965917/2000000000000 : ℝ)^6401 := by
    have hnat : (2176327647 : ℕ)^8449*2000000000000^6401 ≤ 267213965917^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176327647 10000000000 267213965917 2000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344278637/10000000000 : ℝ), (263361623/500000000 : ℝ), (-2176327647/10000000000 : ℝ)] ![(10933701546521/25000000000000 : ℝ), (21452247754097/50000000000000 : ℝ), (267213965917/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344278637/10000000000 : ℝ)|^8449 ≤ (10933701546521/25000000000000 : ℝ)^6401
        have hw : |(5344278637/10000000000 : ℝ)|=(5344278637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263361623/500000000 : ℝ)|^8449 ≤ (21452247754097/50000000000000 : ℝ)^6401
        have hw : |(263361623/500000000 : ℝ)|=(263361623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2176327647/10000000000 : ℝ)|^8449 ≤ (267213965917/2000000000000 : ℝ)^6401
        have hw : |(-2176327647/10000000000 : ℝ)|=(2176327647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s6_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (434884797/1000000000 : ℝ)*x 0 + (4224626819/10000000000 : ℝ)*x 1 + (4476606453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434884797/1000000000 : ℝ)^8449 ≤ (33317473135531/100000000000000 : ℝ)^6401 := by
    have hnat : (434884797 : ℕ)^8449*100000000000000^6401 ≤ 33317473135531^6401*1000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434884797 1000000000 33317473135531 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224626819/10000000000 : ℝ)^8449 ≤ (32067073847561/100000000000000 : ℝ)^6401 := by
    have hnat : (4224626819 : ℕ)^8449*100000000000000^6401 ≤ 32067073847561^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224626819 10000000000 32067073847561 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476606453/10000000000 : ℝ)^8449 ≤ (17307726501739/50000000000000 : ℝ)^6401 := by
    have hnat : (4476606453 : ℕ)^8449*50000000000000^6401 ≤ 17307726501739^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476606453 10000000000 17307726501739 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434884797/1000000000 : ℝ), (4224626819/10000000000 : ℝ), (4476606453/10000000000 : ℝ)] ![(33317473135531/100000000000000 : ℝ), (32067073847561/100000000000000 : ℝ), (17307726501739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434884797/1000000000 : ℝ)|^8449 ≤ (33317473135531/100000000000000 : ℝ)^6401
        have hw : |(434884797/1000000000 : ℝ)|=(434884797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224626819/10000000000 : ℝ)|^8449 ≤ (32067073847561/100000000000000 : ℝ)^6401
        have hw : |(4224626819/10000000000 : ℝ)|=(4224626819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476606453/10000000000 : ℝ)|^8449 ≤ (17307726501739/50000000000000 : ℝ)^6401
        have hw : |(4476606453/10000000000 : ℝ)|=(4476606453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s6_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113522833/10000000000 : ℝ)*x 0 + (2633772731/5000000000 : ℝ)*x 1 + (2695399267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113522833/10000000000 : ℝ)^8449 ≤ (6427068294733/50000000000000 : ℝ)^6401 := by
    have hnat : (2113522833 : ℕ)^8449*50000000000000^6401 ≤ 6427068294733^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113522833 10000000000 6427068294733 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633772731/5000000000 : ℝ)^8449 ≤ (167608831441/390625000000 : ℝ)^6401 := by
    have hnat : (2633772731 : ℕ)^8449*390625000000^6401 ≤ 167608831441^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633772731 5000000000 167608831441 390625000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695399267/5000000000 : ℝ)^8449 ≤ (44238002552979/100000000000000 : ℝ)^6401 := by
    have hnat : (2695399267 : ℕ)^8449*100000000000000^6401 ≤ 44238002552979^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695399267 5000000000 44238002552979 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113522833/10000000000 : ℝ), (2633772731/5000000000 : ℝ), (2695399267/5000000000 : ℝ)] ![(6427068294733/50000000000000 : ℝ), (167608831441/390625000000 : ℝ), (44238002552979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113522833/10000000000 : ℝ)|^8449 ≤ (6427068294733/50000000000000 : ℝ)^6401
        have hw : |(-2113522833/10000000000 : ℝ)|=(2113522833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633772731/5000000000 : ℝ)|^8449 ≤ (167608831441/390625000000 : ℝ)^6401
        have hw : |(2633772731/5000000000 : ℝ)|=(2633772731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695399267/5000000000 : ℝ)|^8449 ≤ (44238002552979/100000000000000 : ℝ)^6401
        have hw : |(2695399267/5000000000 : ℝ)|=(2695399267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s6_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312640727/10000000000 : ℝ)*x 0 + (-64148801/312500000 : ℝ)*x 1 + (5390797953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312640727/10000000000 : ℝ)^8449 ≤ (43393384315789/100000000000000 : ℝ)^6401 := by
    have hnat : (5312640727 : ℕ)^8449*100000000000000^6401 ≤ 43393384315789^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312640727 10000000000 43393384315789 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64148801/312500000 : ℝ)^8449 ≤ (12368619415277/100000000000000 : ℝ)^6401 := by
    have hnat : (64148801 : ℕ)^8449*100000000000000^6401 ≤ 12368619415277^6401*312500000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64148801 312500000 12368619415277 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390797953/10000000000 : ℝ)^8449 ≤ (22118998129857/50000000000000 : ℝ)^6401 := by
    have hnat : (5390797953 : ℕ)^8449*50000000000000^6401 ≤ 22118998129857^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390797953 10000000000 22118998129857 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312640727/10000000000 : ℝ), (-64148801/312500000 : ℝ), (5390797953/10000000000 : ℝ)] ![(43393384315789/100000000000000 : ℝ), (12368619415277/100000000000000 : ℝ), (22118998129857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312640727/10000000000 : ℝ)|^8449 ≤ (43393384315789/100000000000000 : ℝ)^6401
        have hw : |(5312640727/10000000000 : ℝ)|=(5312640727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64148801/312500000 : ℝ)|^8449 ≤ (12368619415277/100000000000000 : ℝ)^6401
        have hw : |(-64148801/312500000 : ℝ)|=(64148801/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390797953/10000000000 : ℝ)|^8449 ≤ (22118998129857/50000000000000 : ℝ)^6401
        have hw : |(5390797953/10000000000 : ℝ)|=(5390797953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s6_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332040063/625000000 : ℝ)*x 0 + (2695398777/5000000000 : ℝ)*x 1 + (-1026380897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332040063/625000000 : ℝ)^8449 ≤ (43393387345331/100000000000000 : ℝ)^6401 := by
    have hnat : (332040063 : ℕ)^8449*100000000000000^6401 ≤ 43393387345331^6401*625000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332040063 625000000 43393387345331 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695398777/5000000000 : ℝ)^8449 ≤ (44237991937833/100000000000000 : ℝ)^6401 := by
    have hnat : (2695398777 : ℕ)^8449*100000000000000^6401 ≤ 44237991937833^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695398777 5000000000 44237991937833 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026380897/5000000000 : ℝ)^8449 ≤ (1236862070369/10000000000000 : ℝ)^6401 := by
    have hnat : (1026380897 : ℕ)^8449*10000000000000^6401 ≤ 1236862070369^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026380897 5000000000 1236862070369 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332040063/625000000 : ℝ), (2695398777/5000000000 : ℝ), (-1026380897/5000000000 : ℝ)] ![(43393387345331/100000000000000 : ℝ), (44237991937833/100000000000000 : ℝ), (1236862070369/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332040063/625000000 : ℝ)|^8449 ≤ (43393387345331/100000000000000 : ℝ)^6401
        have hw : |(332040063/625000000 : ℝ)|=(332040063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695398777/5000000000 : ℝ)|^8449 ≤ (44237991937833/100000000000000 : ℝ)^6401
        have hw : |(2695398777/5000000000 : ℝ)|=(2695398777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026380897/5000000000 : ℝ)|^8449 ≤ (1236862070369/10000000000000 : ℝ)^6401
        have hw : |(-1026380897/5000000000 : ℝ)|=(1026380897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s6_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348857279/10000000000 : ℝ)*x 0 + (4475969121/10000000000 : ℝ)*x 1 + (4225266649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348857279/10000000000 : ℝ)^8449 ≤ (33317567272127/100000000000000 : ℝ)^6401 := by
    have hnat : (4348857279 : ℕ)^8449*100000000000000^6401 ≤ 33317567272127^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348857279 10000000000 33317567272127 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475969121/10000000000 : ℝ)^8449 ≤ (1384357927857/4000000000000 : ℝ)^6401 := by
    have hnat : (4475969121 : ℕ)^8449*4000000000000^6401 ≤ 1384357927857^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475969121 10000000000 1384357927857 4000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225266649/10000000000 : ℝ)^8449 ≤ (32073484519963/100000000000000 : ℝ)^6401 := by
    have hnat : (4225266649 : ℕ)^8449*100000000000000^6401 ≤ 32073484519963^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225266649 10000000000 32073484519963 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348857279/10000000000 : ℝ), (4475969121/10000000000 : ℝ), (4225266649/10000000000 : ℝ)] ![(33317567272127/100000000000000 : ℝ), (1384357927857/4000000000000 : ℝ), (32073484519963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348857279/10000000000 : ℝ)|^8449 ≤ (33317567272127/100000000000000 : ℝ)^6401
        have hw : |(4348857279/10000000000 : ℝ)|=(4348857279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475969121/10000000000 : ℝ)|^8449 ≤ (1384357927857/4000000000000 : ℝ)^6401
        have hw : |(4475969121/10000000000 : ℝ)|=(4475969121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225266649/10000000000 : ℝ)|^8449 ≤ (32073484519963/100000000000000 : ℝ)^6401
        have hw : |(4225266649/10000000000 : ℝ)|=(4225266649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11491/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3529/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1767/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (717/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1767/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (717/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1767/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (717/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1767/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (717/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1767/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (717/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1767/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (717/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (717/6250 : ℝ) ^ (33/8 : ℝ) ≤ (412915767701357/3125000000000000000 : ℝ) := by
    have hpowers : (717/6250 : ℝ)^33 ≤ (412915767701357/3125000000000000000 : ℝ)^8 := by
      have hnat : (717 : ℕ)^33*3125000000000000000^8 ≤ 412915767701357^8*6250^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        717 6250 412915767701357 3125000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (717/6250 : ℝ)) (X := (412915767701357/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (1767/12500 : ℝ) ^ (33/8 : ℝ) ≤ (31267773913104043/100000000000000000000 : ℝ) := by
    have hpowers : (1767/12500 : ℝ)^33 ≤ (31267773913104043/100000000000000000000 : ℝ)^8 := by
      have hnat : (1767 : ℕ)^33*100000000000000000000^8 ≤ 31267773913104043^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1767 12500 31267773913104043 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1767/12500 : ℝ)) (X := (31267773913104043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562912915767701357/1562500000000000000 : ℝ) ≤ (625040036309421/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (1562912915767701357/1562500000000000000 : ℝ)^8 ≤ (625040036309421/625000000000000 : ℝ)^33 := by
      have hnat : (1562912915767701357 : ℕ)^8*625000000000000^33 ≤ 625040036309421^33*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562912915767701357 1562500000000000000 625040036309421 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625040036309421/625000000000000 : ℝ)) (X := (1562912915767701357/1562500000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044481078479547467/100000000000000000000 : ℝ) ≤ (5000539073768031/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100044481078479547467/100000000000000000000 : ℝ)^8 ≤ (5000539073768031/5000000000000000 : ℝ)^33 := by
      have hnat : (100044481078479547467 : ℕ)^8*5000000000000000^33 ≤ 5000539073768031^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044481078479547467 100000000000000000000 5000539073768031 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000539073768031/5000000000000000 : ℝ)) (X := (100044481078479547467/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031267773913104043/50000000000000000000 : ℝ) ≤ (2500378928530347/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50031267773913104043/50000000000000000000 : ℝ)^8 ≤ (2500378928530347/2500000000000000 : ℝ)^33 := by
      have hnat : (50031267773913104043 : ℕ)^8*2500000000000000^33 ≤ 2500378928530347^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031267773913104043 50000000000000000000 2500378928530347 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500378928530347/2500000000000000 : ℝ)) (X := (50031267773913104043/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(412915767701357/3125000000000000000 : ℝ) ≤ ((9247106590249667/9250000000000000 : ℝ)+2*(72927764221/44400000000000 : ℝ)*(717/6250 : ℝ))^(33/8 : ℝ) := by
    rw [show (9247106590249667/9250000000000000 : ℝ)+2*(72927764221/44400000000000 : ℝ)*(717/6250 : ℝ)=(625040036309421/625000000000000 : ℝ) by norm_num, show 1+2*(412915767701357/3125000000000000000 : ℝ)=(1562912915767701357/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31267773913104043/100000000000000000000 : ℝ)+(412915767701357/3125000000000000000 : ℝ) ≤ ((9247106590249667/9250000000000000 : ℝ)+(72927764221/44400000000000 : ℝ)*((1767/12500 : ℝ)+(717/6250 : ℝ)))^(33/8 : ℝ) := by
    rw [show (9247106590249667/9250000000000000 : ℝ)+(72927764221/44400000000000 : ℝ)*((1767/12500 : ℝ)+(717/6250 : ℝ))=(5000539073768031/5000000000000000 : ℝ) by norm_num, show 1+(31267773913104043/100000000000000000000 : ℝ)+(412915767701357/3125000000000000000 : ℝ)=(100044481078479547467/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31267773913104043/100000000000000000000 : ℝ) ≤ ((9247106590249667/9250000000000000 : ℝ)+2*(72927764221/44400000000000 : ℝ)*(1767/12500 : ℝ))^(33/8 : ℝ) := by
    rw [show (9247106590249667/9250000000000000 : ℝ)+2*(72927764221/44400000000000 : ℝ)*(1767/12500 : ℝ)=(2500378928530347/2500000000000000 : ℝ) by norm_num, show 1+2*(31267773913104043/100000000000000000000 : ℝ)=(50031267773913104043/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9247106590249667/9250000000000000 : ℝ)*(X 1 0+X 2 0)+(72927764221/44400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (1767/12500 : ℝ)) (c := (9247106590249667/9250000000000000 : ℝ)) (alpha := (72927764221/44400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9247106590249667/9250000000000000 : ℝ)*(X 0 1+X 2 1)+(72927764221/44400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (1767/12500 : ℝ)) (c := (9247106590249667/9250000000000000 : ℝ)) (alpha := (72927764221/44400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9247106590249667/9250000000000000 : ℝ)*(X 0 2+X 1 2)+(72927764221/44400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (1767/12500 : ℝ)) (c := (9247106590249667/9250000000000000 : ℝ)) (alpha := (72927764221/44400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056758957/5000000000 : ℝ)*X 0 0+(2695556431/5000000000 : ℝ)*X 0 1+(2633616233/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534427863/1000000000 : ℝ)*X 1 0+(-435265531/2000000000 : ℝ)*X 1 1+(5267232461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344278637/10000000000 : ℝ)*X 2 0+(263361623/500000000 : ℝ)*X 2 1+(-2176327647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434884797/1000000000 : ℝ)*X 0 0+(4224626819/10000000000 : ℝ)*X 0 1+(4476606453/10000000000 : ℝ)*X 0 2+(434884797/1000000000 : ℝ)*X 1 0+(4224626819/10000000000 : ℝ)*X 1 1+(4476606453/10000000000 : ℝ)*X 1 2+(434884797/1000000000 : ℝ)*X 2 0+(4224626819/10000000000 : ℝ)*X 2 1+(4476606453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2113522833/10000000000 : ℝ)*X 0 0+(2633772731/5000000000 : ℝ)*X 0 1+(2695399267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312640727/10000000000 : ℝ)*X 1 0+(-64148801/312500000 : ℝ)*X 1 1+(5390797953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332040063/625000000 : ℝ)*X 2 0+(2695398777/5000000000 : ℝ)*X 2 1+(-1026380897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348857279/10000000000 : ℝ)*X 0 0+(4475969121/10000000000 : ℝ)*X 0 1+(4225266649/10000000000 : ℝ)*X 0 2+(4348857279/10000000000 : ℝ)*X 1 0+(4475969121/10000000000 : ℝ)*X 1 1+(4225266649/10000000000 : ℝ)*X 1 2+(4348857279/10000000000 : ℝ)*X 2 0+(4475969121/10000000000 : ℝ)*X 2 1+(4225266649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2362254024010566031176657/231250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396129907/20000000000000 : ℝ)*(base19) + (1850566497/100000000000000 : ℝ)*(base23) + (37585343/50000000000000 : ℝ)*(lower2) + (126983401/50000000000000 : ℝ)*(upper3) + (165919033/100000000000000 : ℝ)*(upper5) + (752565273359867/12500000000000 : ℝ)*(major0) + (752565273359867/12500000000000 : ℝ)*(major1) + (6020522186878937/100000000000000 : ℝ)*(major2) + (100904487892807/1250000000000 : ℝ)*(sp0) + (8072412032889669/100000000000000 : ℝ)*(sp1) + (8072412162972707/100000000000000 : ℝ)*(sp2) + (248037560745439/6250000000000 : ℝ)*(sp3) + (13745528661/25000000000000 : ℝ)*(sp4) + (29047786547/100000000000000 : ℝ)*(sp7) + (992157504928393/25000000000000 : ℝ)*(f.failure) + (8072414013539203/100000000000000 : ℝ)*(f.sum) + (4125547237831/1480000000000000000000000000 : ℝ)*base65 + (29229963723091061/2775000000000000000000000000000 : ℝ)*base67 + (24756666990201937/2775000000000000000000000000000 : ℝ)*base69 + (47697221668291061/2775000000000000000000000000000 : ℝ)*base71 + (7956611528271/1480000000000000000000000000 : ℝ)*base73 + (26390602744373063/2775000000000000000000000000000 : ℝ)*base76 + (1401014956332629/173437500000000000000000000000 : ℝ)*base78 + (3426105921644117/346875000000000000000000000000 : ℝ)*base79 + (1218323914921/138750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (33817719/2500000000000000000000 : ℝ)*base89 + (33817719/2500000000000000000000 : ℝ)*base91 + (8817719/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (618667333471470965591951/231250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1258853633/50000000000000 : ℝ)*(base19) + (679537103/20000000000000 : ℝ)*(base23) + (31969321/12500000000000 : ℝ)*(upper2) + (129141621/50000000000000 : ℝ)*(upper5) + (3025549784634913/50000000000000 : ℝ)*(major0) + (3025549784634913/50000000000000 : ℝ)*(major1) + (3025549784634913/50000000000000 : ℝ)*(major2) + (3918349611/50000000000000 : ℝ)*(sp0) + (15900634079/25000000000000 : ℝ)*(sp1) + (58469786279/100000000000000 : ℝ)*(sp2) + (8113405081251291/100000000000000 : ℝ)*(sp4) + (2028336699426733/25000000000000 : ℝ)*(sp5) + (12677111016373/156250000000 : ℝ)*(sp6) + (1994393065705929/50000000000000 : ℝ)*(sp7) + (1994393065705929/50000000000000 : ℝ)*(f.failure) + (4056706458975257/50000000000000 : ℝ)*(f.sum) + (8073851128963/1110000000000000000000000000 : ℝ)*base65 + (1583205939484981/693750000000000000000000000000 : ℝ)*base68 + (5085499490134981/693750000000000000000000000000 : ℝ)*base70 + (1187187975377519/693750000000000000000000000000 : ℝ)*base71 + (4572399704233/1110000000000000000000000000 : ℝ)*base73 + (5697605539422481/693750000000000000000000000000 : ℝ)*base76 + (316601756678731/693750000000000000000000000000 : ℝ)*base78 + (9754319989197481/693750000000000000000000000000 : ℝ)*base80 + (579774287383/1110000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (11099593/5000000000000000000000 : ℝ)*base90 + (11099593/5000000000000000000000 : ℝ)*base92 + (11099593/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1256_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1256_s7_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056766839/5000000000 : ℝ)*x 0 + (539093133/1000000000 : ℝ)*x 1 + (5267403581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056766839/5000000000 : ℝ)^8449 ≤ (1606777956301/12500000000000 : ℝ)^6401 := by
    have hnat : (1056766839 : ℕ)^8449*12500000000000^6401 ≤ 1606777956301^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056766839 5000000000 1606777956301 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539093133/1000000000 : ℝ)^8449 ≤ (44239440975903/100000000000000 : ℝ)^6401 := by
    have hnat : (539093133 : ℕ)^8449*100000000000000^6401 ≤ 44239440975903^6401*1000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539093133 1000000000 44239440975903 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267403581/10000000000 : ℝ)^8449 ≤ (10726583840551/25000000000000 : ℝ)^6401 := by
    have hnat : (5267403581 : ℕ)^8449*25000000000000^6401 ≤ 10726583840551^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267403581 10000000000 10726583840551 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056766839/5000000000 : ℝ), (539093133/1000000000 : ℝ), (5267403581/10000000000 : ℝ)] ![(1606777956301/12500000000000 : ℝ), (44239440975903/100000000000000 : ℝ), (10726583840551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056766839/5000000000 : ℝ)|^8449 ≤ (1606777956301/12500000000000 : ℝ)^6401
        have hw : |(-1056766839/5000000000 : ℝ)|=(1056766839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539093133/1000000000 : ℝ)|^8449 ≤ (44239440975903/100000000000000 : ℝ)^6401
        have hw : |(539093133/1000000000 : ℝ)|=(539093133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267403581/10000000000 : ℝ)|^8449 ≤ (10726583840551/25000000000000 : ℝ)^6401
        have hw : |(5267403581/10000000000 : ℝ)|=(5267403581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s7_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344232339/10000000000 : ℝ)*x 0 + (-544040417/2500000000 : ℝ)*x 1 + (1053480813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344232339/10000000000 : ℝ)^8449 ≤ (21867153042829/50000000000000 : ℝ)^6401 := by
    have hnat : (5344232339 : ℕ)^8449*50000000000000^6401 ≤ 21867153042829^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344232339 10000000000 21867153042829 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544040417/2500000000 : ℝ)^8449 ≤ (1669919166657/12500000000000 : ℝ)^6401 := by
    have hnat : (544040417 : ℕ)^8449*12500000000000^6401 ≤ 1669919166657^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544040417 2500000000 1669919166657 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053480813/2000000000 : ℝ)^8449 ≤ (5363292570761/12500000000000 : ℝ)^6401 := by
    have hnat : (1053480813 : ℕ)^8449*12500000000000^6401 ≤ 5363292570761^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053480813 2000000000 5363292570761 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344232339/10000000000 : ℝ), (-544040417/2500000000 : ℝ), (1053480813/2000000000 : ℝ)] ![(21867153042829/50000000000000 : ℝ), (1669919166657/12500000000000 : ℝ), (5363292570761/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344232339/10000000000 : ℝ)|^8449 ≤ (21867153042829/50000000000000 : ℝ)^6401
        have hw : |(5344232339/10000000000 : ℝ)|=(5344232339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544040417/2500000000 : ℝ)|^8449 ≤ (1669919166657/12500000000000 : ℝ)^6401
        have hw : |(-544040417/2500000000 : ℝ)|=(544040417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053480813/2000000000 : ℝ)|^8449 ≤ (5363292570761/12500000000000 : ℝ)^6401
        have hw : |(1053480813/2000000000 : ℝ)|=(1053480813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s7_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672116187/5000000000 : ℝ)*x 0 + (658425453/1250000000 : ℝ)*x 1 + (-1088081103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672116187/5000000000 : ℝ)^8449 ≤ (43734306463719/100000000000000 : ℝ)^6401 := by
    have hnat : (2672116187 : ℕ)^8449*100000000000000^6401 ≤ 43734306463719^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672116187 5000000000 43734306463719 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658425453/1250000000 : ℝ)^8449 ≤ (10726583956133/25000000000000 : ℝ)^6401 := by
    have hnat : (658425453 : ℕ)^8449*25000000000000^6401 ≤ 10726583956133^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658425453 1250000000 10726583956133 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088081103/5000000000 : ℝ)^8449 ≤ (1335935769273/10000000000000 : ℝ)^6401 := by
    have hnat : (1088081103 : ℕ)^8449*10000000000000^6401 ≤ 1335935769273^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088081103 5000000000 1335935769273 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672116187/5000000000 : ℝ), (658425453/1250000000 : ℝ), (-1088081103/5000000000 : ℝ)] ![(43734306463719/100000000000000 : ℝ), (10726583956133/25000000000000 : ℝ), (1335935769273/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672116187/5000000000 : ℝ)|^8449 ≤ (43734306463719/100000000000000 : ℝ)^6401
        have hw : |(2672116187/5000000000 : ℝ)|=(2672116187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658425453/1250000000 : ℝ)|^8449 ≤ (10726583956133/25000000000000 : ℝ)^6401
        have hw : |(658425453/1250000000 : ℝ)|=(658425453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088081103/5000000000 : ℝ)|^8449 ≤ (1335935769273/10000000000000 : ℝ)^6401
        have hw : |(-1088081103/5000000000 : ℝ)|=(1088081103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s7_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869771469/2000000000 : ℝ)*x 0 + (422498361/1000000000 : ℝ)*x 1 + (4476246917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869771469/2000000000 : ℝ)^8449 ≤ (8329391984887/25000000000000 : ℝ)^6401 := by
    have hnat : (869771469 : ℕ)^8449*25000000000000^6401 ≤ 8329391984887^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869771469 2000000000 8329391984887 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422498361/1000000000 : ℝ)^8449 ≤ (16035324309261/50000000000000 : ℝ)^6401 := by
    have hnat : (422498361 : ℕ)^8449*50000000000000^6401 ≤ 16035324309261^6401*1000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422498361 1000000000 16035324309261 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476246917/10000000000 : ℝ)^8449 ≤ (34611783431689/100000000000000 : ℝ)^6401 := by
    have hnat : (4476246917 : ℕ)^8449*100000000000000^6401 ≤ 34611783431689^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476246917 10000000000 34611783431689 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869771469/2000000000 : ℝ), (422498361/1000000000 : ℝ), (4476246917/10000000000 : ℝ)] ![(8329391984887/25000000000000 : ℝ), (16035324309261/50000000000000 : ℝ), (34611783431689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869771469/2000000000 : ℝ)|^8449 ≤ (8329391984887/25000000000000 : ℝ)^6401
        have hw : |(869771469/2000000000 : ℝ)|=(869771469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422498361/1000000000 : ℝ)|^8449 ≤ (16035324309261/50000000000000 : ℝ)^6401
        have hw : |(422498361/1000000000 : ℝ)|=(422498361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476246917/10000000000 : ℝ)|^8449 ≤ (34611783431689/100000000000000 : ℝ)^6401
        have hw : |(4476246917/10000000000 : ℝ)|=(4476246917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s7_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056769161/5000000000 : ℝ)*x 0 + (5267715229/10000000000 : ℝ)*x 1 + (5390618537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056769161/5000000000 : ℝ)^8449 ≤ (321356523283/2500000000000 : ℝ)^6401 := by
    have hnat : (1056769161 : ℕ)^8449*2500000000000^6401 ≤ 321356523283^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056769161 5000000000 321356523283 2500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267715229/10000000000 : ℝ)^8449 ≤ (21454843089817/50000000000000 : ℝ)^6401 := by
    have hnat : (5267715229 : ℕ)^8449*50000000000000^6401 ≤ 21454843089817^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267715229 10000000000 21454843089817 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390618537/10000000000 : ℝ)^8449 ≤ (44236052875219/100000000000000 : ℝ)^6401 := by
    have hnat : (5390618537 : ℕ)^8449*100000000000000^6401 ≤ 44236052875219^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390618537 10000000000 44236052875219 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056769161/5000000000 : ℝ), (5267715229/10000000000 : ℝ), (5390618537/10000000000 : ℝ)] ![(321356523283/2500000000000 : ℝ), (21454843089817/50000000000000 : ℝ), (44236052875219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056769161/5000000000 : ℝ)|^8449 ≤ (321356523283/2500000000000 : ℝ)^6401
        have hw : |(-1056769161/5000000000 : ℝ)|=(1056769161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267715229/10000000000 : ℝ)|^8449 ≤ (21454843089817/50000000000000 : ℝ)^6401
        have hw : |(5267715229/10000000000 : ℝ)|=(5267715229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390618537/10000000000 : ℝ)|^8449 ≤ (44236052875219/100000000000000 : ℝ)^6401
        have hw : |(5390618537/10000000000 : ℝ)|=(5390618537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s7_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312684083/10000000000 : ℝ)*x 0 + (-513236799/2500000000 : ℝ)*x 1 + (2695309273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312684083/10000000000 : ℝ)^8449 ≤ (21696925874913/50000000000000 : ℝ)^6401 := by
    have hnat : (5312684083 : ℕ)^8449*50000000000000^6401 ≤ 21696925874913^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312684083 10000000000 21696925874913 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513236799/2500000000 : ℝ)^8449 ≤ (1546261907299/12500000000000 : ℝ)^6401 := by
    have hnat : (513236799 : ℕ)^8449*12500000000000^6401 ≤ 1546261907299^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513236799 2500000000 1546261907299 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695309273/5000000000 : ℝ)^8449 ≤ (1382376655397/3125000000000 : ℝ)^6401 := by
    have hnat : (2695309273 : ℕ)^8449*3125000000000^6401 ≤ 1382376655397^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695309273 5000000000 1382376655397 3125000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312684083/10000000000 : ℝ), (-513236799/2500000000 : ℝ), (2695309273/5000000000 : ℝ)] ![(21696925874913/50000000000000 : ℝ), (1546261907299/12500000000000 : ℝ), (1382376655397/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312684083/10000000000 : ℝ)|^8449 ≤ (21696925874913/50000000000000 : ℝ)^6401
        have hw : |(5312684083/10000000000 : ℝ)|=(5312684083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513236799/2500000000 : ℝ)|^8449 ≤ (1546261907299/12500000000000 : ℝ)^6401
        have hw : |(-513236799/2500000000 : ℝ)|=(513236799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695309273/5000000000 : ℝ)|^8449 ≤ (1382376655397/3125000000000 : ℝ)^6401
        have hw : |(2695309273/5000000000 : ℝ)|=(2695309273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s7_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312684089/10000000000 : ℝ)*x 0 + (1078123707/2000000000 : ℝ)*x 1 + (-2052947203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312684089/10000000000 : ℝ)^8449 ≤ (21696925907257/50000000000000 : ℝ)^6401 := by
    have hnat : (5312684089 : ℕ)^8449*50000000000000^6401 ≤ 21696925907257^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312684089 10000000000 21696925907257 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078123707/2000000000 : ℝ)^8449 ≤ (8847210570711/20000000000000 : ℝ)^6401 := by
    have hnat : (1078123707 : ℕ)^8449*20000000000000^6401 ≤ 8847210570711^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078123707 2000000000 8847210570711 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052947203/10000000000 : ℝ)^8449 ≤ (2474019062813/20000000000000 : ℝ)^6401 := by
    have hnat : (2052947203 : ℕ)^8449*20000000000000^6401 ≤ 2474019062813^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052947203 10000000000 2474019062813 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312684089/10000000000 : ℝ), (1078123707/2000000000 : ℝ), (-2052947203/10000000000 : ℝ)] ![(21696925907257/50000000000000 : ℝ), (8847210570711/20000000000000 : ℝ), (2474019062813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312684089/10000000000 : ℝ)|^8449 ≤ (21696925907257/50000000000000 : ℝ)^6401
        have hw : |(5312684089/10000000000 : ℝ)|=(5312684089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078123707/2000000000 : ℝ)|^8449 ≤ (8847210570711/20000000000000 : ℝ)^6401
        have hw : |(1078123707/2000000000 : ℝ)|=(1078123707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2052947203/10000000000 : ℝ)|^8449 ≤ (2474019062813/20000000000000 : ℝ)^6401
        have hw : |(-2052947203/10000000000 : ℝ)|=(2052947203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s7_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174433139/5000000000 : ℝ)*x 0 + (4475612757/10000000000 : ℝ)*x 1 + (2112810277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174433139/5000000000 : ℝ)^8449 ≤ (8329414568483/25000000000000 : ℝ)^6401 := by
    have hnat : (2174433139 : ℕ)^8449*25000000000000^6401 ≤ 8329414568483^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174433139 5000000000 8329414568483 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475612757/10000000000 : ℝ)^8449 ≤ (692106223293/2000000000000 : ℝ)^6401 := by
    have hnat : (4475612757 : ℕ)^8449*2000000000000^6401 ≤ 692106223293^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475612757 10000000000 692106223293 2000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112810277/5000000000 : ℝ)^8449 ≤ (32077030546847/100000000000000 : ℝ)^6401 := by
    have hnat : (2112810277 : ℕ)^8449*100000000000000^6401 ≤ 32077030546847^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112810277 5000000000 32077030546847 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174433139/5000000000 : ℝ), (4475612757/10000000000 : ℝ), (2112810277/5000000000 : ℝ)] ![(8329414568483/25000000000000 : ℝ), (692106223293/2000000000000 : ℝ), (32077030546847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174433139/5000000000 : ℝ)|^8449 ≤ (8329414568483/25000000000000 : ℝ)^6401
        have hw : |(2174433139/5000000000 : ℝ)|=(2174433139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475612757/10000000000 : ℝ)|^8449 ≤ (692106223293/2000000000000 : ℝ)^6401
        have hw : |(4475612757/10000000000 : ℝ)|=(4475612757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112810277/5000000000 : ℝ)|^8449 ≤ (32077030546847/100000000000000 : ℝ)^6401
        have hw : |(2112810277/5000000000 : ℝ)|=(2112810277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2299/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11491/100000 : ℝ) ^ (33/8 : ℝ) ≤ (13303809780969417/100000000000000000000 : ℝ) := by
    have hpowers : (11491/100000 : ℝ)^33 ≤ (13303809780969417/100000000000000000000 : ℝ)^8 := by
      have hnat : (11491 : ℕ)^33*100000000000000000000^8 ≤ 13303809780969417^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11491 100000 13303809780969417 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11491/100000 : ℝ)) (X := (13303809780969417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (3529/25000 : ℝ) ^ (33/8 : ℝ) ≤ (7771423273815381/25000000000000000000 : ℝ) := by
    have hpowers : (3529/25000 : ℝ)^33 ≤ (7771423273815381/25000000000000000000 : ℝ)^8 := by
      have hnat : (3529 : ℕ)^33*25000000000000000000^8 ≤ 7771423273815381^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3529 25000 7771423273815381 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3529/25000 : ℝ)) (X := (7771423273815381/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013303809780969417/50000000000000000000 : ℝ) ≤ (2500161242050259/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50013303809780969417/50000000000000000000 : ℝ)^8 ≤ (2500161242050259/2500000000000000 : ℝ)^33 := by
      have hnat : (50013303809780969417 : ℕ)^8*2500000000000000^33 ≤ 2500161242050259^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013303809780969417 50000000000000000000 2500161242050259 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500161242050259/2500000000000000 : ℝ)) (X := (50013303809780969417/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044389502876230941/100000000000000000000 : ℝ) ≤ (1000107592826847/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100044389502876230941/100000000000000000000 : ℝ)^8 ≤ (1000107592826847/1000000000000000 : ℝ)^33 := by
      have hnat : (100044389502876230941 : ℕ)^8*1000000000000000^33 ≤ 1000107592826847^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044389502876230941 100000000000000000000 1000107592826847 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000107592826847/1000000000000000 : ℝ)) (X := (100044389502876230941/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507771423273815381/12500000000000000000 : ℝ) ≤ (312547090260497/312500000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12507771423273815381/12500000000000000000 : ℝ)^8 ≤ (312547090260497/312500000000000 : ℝ)^33 := by
      have hnat : (12507771423273815381 : ℕ)^8*312500000000000^33 ≤ 312547090260497^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507771423273815381 12500000000000000000 312547090260497 312500000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312547090260497/312500000000000 : ℝ)) (X := (12507771423273815381/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13303809780969417/100000000000000000000 : ℝ) ≤ ((1640111794828621957/1640625000000000000 : ℝ)+2*(215480033717/131250000000000 : ℝ)*(11491/100000 : ℝ))^(33/8 : ℝ) := by
    rw [show (1640111794828621957/1640625000000000000 : ℝ)+2*(215480033717/131250000000000 : ℝ)*(11491/100000 : ℝ)=(2500161242050259/2500000000000000 : ℝ) by norm_num, show 1+2*(13303809780969417/100000000000000000000 : ℝ)=(50013303809780969417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7771423273815381/25000000000000000000 : ℝ)+(13303809780969417/100000000000000000000 : ℝ) ≤ ((1640111794828621957/1640625000000000000 : ℝ)+(215480033717/131250000000000 : ℝ)*((3529/25000 : ℝ)+(11491/100000 : ℝ)))^(33/8 : ℝ) := by
    rw [show (1640111794828621957/1640625000000000000 : ℝ)+(215480033717/131250000000000 : ℝ)*((3529/25000 : ℝ)+(11491/100000 : ℝ))=(1000107592826847/1000000000000000 : ℝ) by norm_num, show 1+(7771423273815381/25000000000000000000 : ℝ)+(13303809780969417/100000000000000000000 : ℝ)=(100044389502876230941/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7771423273815381/25000000000000000000 : ℝ) ≤ ((1640111794828621957/1640625000000000000 : ℝ)+2*(215480033717/131250000000000 : ℝ)*(3529/25000 : ℝ))^(33/8 : ℝ) := by
    rw [show (1640111794828621957/1640625000000000000 : ℝ)+2*(215480033717/131250000000000 : ℝ)*(3529/25000 : ℝ)=(312547090260497/312500000000000 : ℝ) by norm_num, show 1+2*(7771423273815381/25000000000000000000 : ℝ)=(12507771423273815381/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1640111794828621957/1640625000000000000 : ℝ)*(X 1 0+X 2 0)+(215480033717/131250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (11491/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1640111794828621957/1640625000000000000 : ℝ)) (alpha := (215480033717/131250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1640111794828621957/1640625000000000000 : ℝ)*(X 0 1+X 2 1)+(215480033717/131250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (11491/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1640111794828621957/1640625000000000000 : ℝ)) (alpha := (215480033717/131250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1640111794828621957/1640625000000000000 : ℝ)*(X 0 2+X 1 2)+(215480033717/131250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (11491/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1640111794828621957/1640625000000000000 : ℝ)) (alpha := (215480033717/131250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056766839/5000000000 : ℝ)*X 0 0+(539093133/1000000000 : ℝ)*X 0 1+(5267403581/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344232339/10000000000 : ℝ)*X 1 0+(-544040417/2500000000 : ℝ)*X 1 1+(1053480813/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672116187/5000000000 : ℝ)*X 2 0+(658425453/1250000000 : ℝ)*X 2 1+(-1088081103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869771469/2000000000 : ℝ)*X 0 0+(422498361/1000000000 : ℝ)*X 0 1+(4476246917/10000000000 : ℝ)*X 0 2+(869771469/2000000000 : ℝ)*X 1 0+(422498361/1000000000 : ℝ)*X 1 1+(4476246917/10000000000 : ℝ)*X 1 2+(869771469/2000000000 : ℝ)*X 2 0+(422498361/1000000000 : ℝ)*X 2 1+(4476246917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1056769161/5000000000 : ℝ)*X 0 0+(5267715229/10000000000 : ℝ)*X 0 1+(5390618537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312684083/10000000000 : ℝ)*X 1 0+(-513236799/2500000000 : ℝ)*X 1 1+(2695309273/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312684089/10000000000 : ℝ)*X 2 0+(1078123707/2000000000 : ℝ)*X 2 1+(-2052947203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174433139/5000000000 : ℝ)*X 0 0+(4475612757/10000000000 : ℝ)*X 0 1+(2112810277/5000000000 : ℝ)*X 0 2+(2174433139/5000000000 : ℝ)*X 1 0+(4475612757/10000000000 : ℝ)*X 1 1+(2112810277/5000000000 : ℝ)*X 1 2+(2174433139/5000000000 : ℝ)*X 2 0+(4475612757/10000000000 : ℝ)*X 2 1+(2112810277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34184045856622331867546483/5468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1155197667/100000000000000 : ℝ)*(base19) + (412462547/25000000000000 : ℝ)*(base23) + (109250271/25000000000000 : ℝ)*(upper3) + (249351941/100000000000000 : ℝ)*(lower4) + (3018854276459173/50000000000000 : ℝ)*(major0) + (3018854276459173/50000000000000 : ℝ)*(major1) + (6037708552918347/100000000000000 : ℝ)*(major2) + (8095417202155321/100000000000000 : ℝ)*(sp0) + (1619091350082771/20000000000000 : ℝ)*(sp1) + (8095452029782869/100000000000000 : ℝ)*(sp2) + (3979920548749419/100000000000000 : ℝ)*(sp3) + (20351728101/50000000000000 : ℝ)*(sp4) + (132061827/3125000000000 : ℝ)*(sp6) + (9610778961/25000000000000 : ℝ)*(sp7) + (1989979495932631/50000000000000 : ℝ)*(f.failure) + (4047728952805761/50000000000000 : ℝ)*(f.sum) + (1967787954473/468750000000000000000000000 : ℝ)*base66 + (1546398378244082189/82031250000000000000000000000000 : ℝ)*base68 + (383529507856495079/164062500000000000000000000000000 : ℝ)*base69 + (650497883189394689/82031250000000000000000000000000 : ℝ)*base72 + (1148089667267/1875000000000000000000000000 : ℝ)*base74 + (541538167231495079/164062500000000000000000000000000 : ℝ)*base75 + (760552729482157189/82031250000000000000000000000000 : ℝ)*base78 + (312185544345438439/82031250000000000000000000000000 : ℝ)*base80 + (62852196086039/13125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (3212073/5000000000000000000000 : ℝ)*base89 + (3212073/5000000000000000000000 : ℝ)*base91 + (46787927/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41887740434404608768537061/6835937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (273496611/25000000000000 : ℝ)*(base19) + (300206759/25000000000000 : ℝ)*(base23) + (64518079/50000000000000 : ℝ)*(upper3) + (22120263/50000000000000 : ℝ)*(lower4) + (29866951/25000000000000 : ℝ)*(upper5) + (6068300333723029/100000000000000 : ℝ)*(major0) + (6068300333723029/100000000000000 : ℝ)*(major1) + (6068300333723029/100000000000000 : ℝ)*(major2) + (31047223379/100000000000000 : ℝ)*(sp1) + (33468442647/100000000000000 : ℝ)*(sp2) + (8136475868430387/100000000000000 : ℝ)*(sp4) + (8136443727220563/100000000000000 : ℝ)*(sp5) + (63565946868443/781250000000 : ℝ)*(sp6) + (250007787172691/6250000000000 : ℝ)*(sp7) + (250007787172691/6250000000000 : ℝ)*(f.failure) + (8136475868430387/100000000000000 : ℝ)*(f.sum) + (853661405987/102539062500000000000000000 : ℝ)*base65 + (961698381527577247/164062500000000000000000000000000 : ℝ)*base68 + (1395786584191172753/164062500000000000000000000000000 : ℝ)*base69 + (4188500962042735253/164062500000000000000000000000000 : ℝ)*base71 + (32013264166207/6562500000000000000000000000 : ℝ)*base74 + (51833635019297753/164062500000000000000000000000000 : ℝ)*base75 + (1454327142480235253/164062500000000000000000000000000 : ℝ)*base77 + (2985032144683360253/164062500000000000000000000000000 : ℝ)*base79 + (33340529773459/3281250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4950947/625000000000000000000 : ℝ)*base90 + (4950947/625000000000000000000 : ℝ)*base92 + (4950947/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1256_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1256_s8_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056768251/5000000000 : ℝ)*x 0 + (5390894777/10000000000 : ℝ)*x 1 + (5267438297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056768251/5000000000 : ℝ)^8449 ≤ (3213561580199/25000000000000 : ℝ)^6401 := by
    have hnat : (1056768251 : ℕ)^8449*25000000000000^6401 ≤ 3213561580199^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056768251 5000000000 3213561580199 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390894777/10000000000 : ℝ)^8449 ≤ (44239045039103/100000000000000 : ℝ)^6401 := by
    have hnat : (5390894777 : ℕ)^8449*100000000000000^6401 ≤ 44239045039103^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390894777 10000000000 44239045039103 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267438297/10000000000 : ℝ)^8449 ≤ (42906708623061/100000000000000 : ℝ)^6401 := by
    have hnat : (5267438297 : ℕ)^8449*100000000000000^6401 ≤ 42906708623061^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267438297 10000000000 42906708623061 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056768251/5000000000 : ℝ), (5390894777/10000000000 : ℝ), (5267438297/10000000000 : ℝ)] ![(3213561580199/25000000000000 : ℝ), (44239045039103/100000000000000 : ℝ), (42906708623061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056768251/5000000000 : ℝ)|^8449 ≤ (3213561580199/25000000000000 : ℝ)^6401
        have hw : |(-1056768251/5000000000 : ℝ)|=(1056768251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390894777/10000000000 : ℝ)|^8449 ≤ (44239045039103/100000000000000 : ℝ)^6401
        have hw : |(5390894777/10000000000 : ℝ)|=(5390894777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267438297/10000000000 : ℝ)|^8449 ≤ (42906708623061/100000000000000 : ℝ)^6401
        have hw : |(5267438297/10000000000 : ℝ)|=(5267438297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s8_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344223223/10000000000 : ℝ)*x 0 + (-10880639/50000000 : ℝ)*x 1 + (1316859687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344223223/10000000000 : ℝ)^8449 ≤ (4373420761687/10000000000000 : ℝ)^6401 := by
    have hnat : (5344223223 : ℕ)^8449*10000000000000^6401 ≤ 4373420761687^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344223223 10000000000 4373420761687 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10880639/50000000 : ℝ)^8449 ≤ (104367803889/781250000000 : ℝ)^6401 := by
    have hnat : (10880639 : ℕ)^8449*781250000000^6401 ≤ 104367803889^6401*50000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10880639 50000000 104367803889 781250000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316859687/2500000000 : ℝ)^8449 ≤ (8581342694429/20000000000000 : ℝ)^6401 := by
    have hnat : (1316859687 : ℕ)^8449*20000000000000^6401 ≤ 8581342694429^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316859687 2500000000 8581342694429 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344223223/10000000000 : ℝ), (-10880639/50000000 : ℝ), (1316859687/2500000000 : ℝ)] ![(4373420761687/10000000000000 : ℝ), (104367803889/781250000000 : ℝ), (8581342694429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344223223/10000000000 : ℝ)|^8449 ≤ (4373420761687/10000000000000 : ℝ)^6401
        have hw : |(5344223223/10000000000 : ℝ)|=(5344223223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10880639/50000000 : ℝ)|^8449 ≤ (104367803889/781250000000 : ℝ)^6401
        have hw : |(-10880639/50000000 : ℝ)|=(10880639/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316859687/2500000000 : ℝ)|^8449 ≤ (8581342694429/20000000000000 : ℝ)^6401
        have hw : |(1316859687/2500000000 : ℝ)|=(1316859687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s8_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068844689/2000000000 : ℝ)*x 0 + (658429803/1250000000 : ℝ)*x 1 + (-1088063967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068844689/2000000000 : ℝ)^8449 ≤ (43734210014859/100000000000000 : ℝ)^6401 := by
    have hnat : (1068844689 : ℕ)^8449*100000000000000^6401 ≤ 43734210014859^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068844689 2000000000 43734210014859 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658429803/1250000000 : ℝ)^8449 ≤ (21453354994273/50000000000000 : ℝ)^6401 := by
    have hnat : (658429803 : ℕ)^8449*50000000000000^6401 ≤ 21453354994273^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658429803 1250000000 21453354994273 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088063967/5000000000 : ℝ)^8449 ≤ (13359079983603/100000000000000 : ℝ)^6401 := by
    have hnat : (1088063967 : ℕ)^8449*100000000000000^6401 ≤ 13359079983603^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088063967 5000000000 13359079983603 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068844689/2000000000 : ℝ), (658429803/1250000000 : ℝ), (-1088063967/5000000000 : ℝ)] ![(43734210014859/100000000000000 : ℝ), (21453354994273/50000000000000 : ℝ), (13359079983603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068844689/2000000000 : ℝ)|^8449 ≤ (43734210014859/100000000000000 : ℝ)^6401
        have hw : |(1068844689/2000000000 : ℝ)|=(1068844689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658429803/1250000000 : ℝ)|^8449 ≤ (21453354994273/50000000000000 : ℝ)^6401
        have hw : |(658429803/1250000000 : ℝ)|=(658429803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088063967/5000000000 : ℝ)|^8449 ≤ (13359079983603/100000000000000 : ℝ)^6401
        have hw : |(-1088063967/5000000000 : ℝ)|=(1088063967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s8_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174429517/5000000000 : ℝ)*x 0 + (2112528429/5000000000 : ℝ)*x 1 + (559521667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174429517/5000000000 : ℝ)^8449 ≤ (16658792509723/50000000000000 : ℝ)^6401 := by
    have hnat : (2174429517 : ℕ)^8449*50000000000000^6401 ≤ 16658792509723^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174429517 5000000000 16658792509723 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112528429/5000000000 : ℝ)^8449 ≤ (6414276503801/20000000000000 : ℝ)^6401 := by
    have hnat : (2112528429 : ℕ)^8449*20000000000000^6401 ≤ 6414276503801^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112528429 5000000000 6414276503801 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559521667/1250000000 : ℝ)^8449 ≤ (34611032445467/100000000000000 : ℝ)^6401 := by
    have hnat : (559521667 : ℕ)^8449*100000000000000^6401 ≤ 34611032445467^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559521667 1250000000 34611032445467 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174429517/5000000000 : ℝ), (2112528429/5000000000 : ℝ), (559521667/1250000000 : ℝ)] ![(16658792509723/50000000000000 : ℝ), (6414276503801/20000000000000 : ℝ), (34611032445467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174429517/5000000000 : ℝ)|^8449 ≤ (16658792509723/50000000000000 : ℝ)^6401
        have hw : |(2174429517/5000000000 : ℝ)|=(2174429517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112528429/5000000000 : ℝ)|^8449 ≤ (6414276503801/20000000000000 : ℝ)^6401
        have hw : |(2112528429/5000000000 : ℝ)|=(2112528429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559521667/1250000000 : ℝ)|^8449 ≤ (34611032445467/100000000000000 : ℝ)^6401
        have hw : |(559521667/1250000000 : ℝ)|=(559521667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s8_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113540803/10000000000 : ℝ)*x 0 + (5267749761/10000000000 : ℝ)*x 1 + (269529121/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113540803/10000000000 : ℝ)^8449 ≤ (64271404241/500000000000 : ℝ)^6401 := by
    have hnat : (2113540803 : ℕ)^8449*500000000000^6401 ≤ 64271404241^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113540803 10000000000 64271404241 500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267749761/10000000000 : ℝ)^8449 ≤ (21455028734589/50000000000000 : ℝ)^6401 := by
    have hnat : (5267749761 : ℕ)^8449*50000000000000^6401 ≤ 21455028734589^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267749761 10000000000 21455028734589 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269529121/500000000 : ℝ)^8449 ≤ (8847132333673/20000000000000 : ℝ)^6401 := by
    have hnat : (269529121 : ℕ)^8449*20000000000000^6401 ≤ 8847132333673^6401*500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269529121 500000000 8847132333673 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113540803/10000000000 : ℝ), (5267749761/10000000000 : ℝ), (269529121/500000000 : ℝ)] ![(64271404241/500000000000 : ℝ), (21455028734589/50000000000000 : ℝ), (8847132333673/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113540803/10000000000 : ℝ)|^8449 ≤ (64271404241/500000000000 : ℝ)^6401
        have hw : |(-2113540803/10000000000 : ℝ)|=(2113540803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267749761/10000000000 : ℝ)|^8449 ≤ (21455028734589/50000000000000 : ℝ)^6401
        have hw : |(5267749761/10000000000 : ℝ)|=(5267749761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269529121/500000000 : ℝ)|^8449 ≤ (8847132333673/20000000000000 : ℝ)^6401
        have hw : |(269529121/500000000 : ℝ)|=(269529121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s8_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312693459/10000000000 : ℝ)*x 0 + (-2052984151/10000000000 : ℝ)*x 1 + (2695291039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312693459/10000000000 : ℝ)^8449 ≤ (21696976417727/50000000000000 : ℝ)^6401 := by
    have hnat : (5312693459 : ℕ)^8449*50000000000000^6401 ≤ 21696976417727^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312693459 10000000000 21696976417727 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052984151/10000000000 : ℝ)^8449 ≤ (12370389177083/100000000000000 : ℝ)^6401 := by
    have hnat : (2052984151 : ℕ)^8449*100000000000000^6401 ≤ 12370389177083^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052984151 10000000000 12370389177083 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695291039/5000000000 : ℝ)^8449 ≤ (44235657963943/100000000000000 : ℝ)^6401 := by
    have hnat : (2695291039 : ℕ)^8449*100000000000000^6401 ≤ 44235657963943^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695291039 5000000000 44235657963943 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312693459/10000000000 : ℝ), (-2052984151/10000000000 : ℝ), (2695291039/5000000000 : ℝ)] ![(21696976417727/50000000000000 : ℝ), (12370389177083/100000000000000 : ℝ), (44235657963943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312693459/10000000000 : ℝ)|^8449 ≤ (21696976417727/50000000000000 : ℝ)^6401
        have hw : |(5312693459/10000000000 : ℝ)|=(5312693459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2052984151/10000000000 : ℝ)|^8449 ≤ (12370389177083/100000000000000 : ℝ)^6401
        have hw : |(-2052984151/10000000000 : ℝ)|=(2052984151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695291039/5000000000 : ℝ)|^8449 ≤ (44235657963943/100000000000000 : ℝ)^6401
        have hw : |(2695291039/5000000000 : ℝ)|=(2695291039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s8_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062538613/2000000000 : ℝ)*x 0 + (1347645603/2500000000 : ℝ)*x 1 + (-256623029/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062538613/2000000000 : ℝ)^8449 ≤ (21696974293807/50000000000000 : ℝ)^6401 := by
    have hnat : (1062538613 : ℕ)^8449*50000000000000^6401 ≤ 21696974293807^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062538613 2000000000 21696974293807 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347645603/2500000000 : ℝ)^8449 ≤ (2764728848857/6250000000000 : ℝ)^6401 := by
    have hnat : (1347645603 : ℕ)^8449*6250000000000^6401 ≤ 2764728848857^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347645603 2500000000 2764728848857 6250000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256623029/1250000000 : ℝ)^8449 ≤ (96643670479/781250000000 : ℝ)^6401 := by
    have hnat : (256623029 : ℕ)^8449*781250000000^6401 ≤ 96643670479^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256623029 1250000000 96643670479 781250000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062538613/2000000000 : ℝ), (1347645603/2500000000 : ℝ), (-256623029/1250000000 : ℝ)] ![(21696974293807/50000000000000 : ℝ), (2764728848857/6250000000000 : ℝ), (96643670479/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062538613/2000000000 : ℝ)|^8449 ≤ (21696974293807/50000000000000 : ℝ)^6401
        have hw : |(1062538613/2000000000 : ℝ)|=(1062538613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347645603/2500000000 : ℝ)|^8449 ≤ (2764728848857/6250000000000 : ℝ)^6401
        have hw : |(1347645603/2500000000 : ℝ)|=(1347645603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256623029/1250000000 : ℝ)|^8449 ≤ (96643670479/781250000000 : ℝ)^6401
        have hw : |(-256623029/1250000000 : ℝ)|=(256623029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s8_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087216997/2500000000 : ℝ)*x 0 + (2237770103/5000000000 : ℝ)*x 1 + (2112846363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087216997/2500000000 : ℝ)^8449 ≤ (33317675566203/100000000000000 : ℝ)^6401 := by
    have hnat : (1087216997 : ℕ)^8449*100000000000000^6401 ≤ 33317675566203^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087216997 2500000000 33317675566203 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237770103/5000000000 : ℝ)^8449 ≤ (17302285362203/50000000000000 : ℝ)^6401 := by
    have hnat : (2237770103 : ℕ)^8449*50000000000000^6401 ≤ 17302285362203^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237770103 5000000000 17302285362203 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112846363/5000000000 : ℝ)^8449 ≤ (32077753701311/100000000000000 : ℝ)^6401 := by
    have hnat : (2112846363 : ℕ)^8449*100000000000000^6401 ≤ 32077753701311^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112846363 5000000000 32077753701311 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087216997/2500000000 : ℝ), (2237770103/5000000000 : ℝ), (2112846363/5000000000 : ℝ)] ![(33317675566203/100000000000000 : ℝ), (17302285362203/50000000000000 : ℝ), (32077753701311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087216997/2500000000 : ℝ)|^8449 ≤ (33317675566203/100000000000000 : ℝ)^6401
        have hw : |(1087216997/2500000000 : ℝ)|=(1087216997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237770103/5000000000 : ℝ)|^8449 ≤ (17302285362203/50000000000000 : ℝ)^6401
        have hw : |(2237770103/5000000000 : ℝ)|=(2237770103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112846363/5000000000 : ℝ)|^8449 ≤ (32077753701311/100000000000000 : ℝ)^6401
        have hw : |(2112846363/5000000000 : ℝ)|=(2112846363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1437/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14111/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2299/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2299/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2299/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2299/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2299/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2299/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2299/20000 : ℝ) ^ (33/8 : ℝ) ≤ (13322923198838589/100000000000000000000 : ℝ) := by
    have hpowers : (2299/20000 : ℝ)^33 ≤ (13322923198838589/100000000000000000000 : ℝ)^8 := by
      have hnat : (2299 : ℕ)^33*100000000000000000000^8 ≤ 13322923198838589^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2299 20000 13322923198838589 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2299/20000 : ℝ)) (X := (13322923198838589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (441/3125 : ℝ) ^ (33/8 : ℝ) ≤ (31049373537038073/100000000000000000000 : ℝ) := by
    have hpowers : (441/3125 : ℝ)^33 ≤ (31049373537038073/100000000000000000000 : ℝ)^8 := by
      have hnat : (441 : ℕ)^33*100000000000000000000^8 ≤ 31049373537038073^8*3125^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 3125 31049373537038073 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/3125 : ℝ)) (X := (31049373537038073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013322923198838589/50000000000000000000 : ℝ) ≤ (2000129178945063/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50013322923198838589/50000000000000000000 : ℝ)^8 ≤ (2000129178945063/2000000000000000 : ℝ)^33 := by
      have hnat : (50013322923198838589 : ℕ)^8*2000000000000000^33 ≤ 2000129178945063^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013322923198838589 50000000000000000000 2000129178945063 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000129178945063/2000000000000000 : ℝ)) (X := (50013322923198838589/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022186148367938331/50000000000000000000 : ℝ) ≤ (1250134438911263/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50022186148367938331/50000000000000000000 : ℝ)^8 ≤ (1250134438911263/1250000000000000 : ℝ)^33 := by
      have hnat : (50022186148367938331 : ℕ)^8*1250000000000000^33 ≤ 1250134438911263^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022186148367938331 50000000000000000000 1250134438911263 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250134438911263/1250000000000000 : ℝ)) (X := (50022186148367938331/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031049373537038073/50000000000000000000 : ℝ) ≤ (10001505127854893/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50031049373537038073/50000000000000000000 : ℝ)^8 ≤ (10001505127854893/10000000000000000 : ℝ)^33 := by
      have hnat : (50031049373537038073 : ℕ)^8*10000000000000000^33 ≤ 10001505127854893^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031049373537038073 50000000000000000000 10001505127854893 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001505127854893/10000000000000000 : ℝ)) (X := (50031049373537038073/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13322923198838589/100000000000000000000 : ℝ) ≤ ((5232362684334330049/5234000000000000000 : ℝ)+2*(429616564789/261700000000000 : ℝ)*(2299/20000 : ℝ))^(33/8 : ℝ) := by
    rw [show (5232362684334330049/5234000000000000000 : ℝ)+2*(429616564789/261700000000000 : ℝ)*(2299/20000 : ℝ)=(2000129178945063/2000000000000000 : ℝ) by norm_num, show 1+2*(13322923198838589/100000000000000000000 : ℝ)=(50013322923198838589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31049373537038073/100000000000000000000 : ℝ)+(13322923198838589/100000000000000000000 : ℝ) ≤ ((5232362684334330049/5234000000000000000 : ℝ)+(429616564789/261700000000000 : ℝ)*((441/3125 : ℝ)+(2299/20000 : ℝ)))^(33/8 : ℝ) := by
    rw [show (5232362684334330049/5234000000000000000 : ℝ)+(429616564789/261700000000000 : ℝ)*((441/3125 : ℝ)+(2299/20000 : ℝ))=(1250134438911263/1250000000000000 : ℝ) by norm_num, show 1+(31049373537038073/100000000000000000000 : ℝ)+(13322923198838589/100000000000000000000 : ℝ)=(50022186148367938331/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31049373537038073/100000000000000000000 : ℝ) ≤ ((5232362684334330049/5234000000000000000 : ℝ)+2*(429616564789/261700000000000 : ℝ)*(441/3125 : ℝ))^(33/8 : ℝ) := by
    rw [show (5232362684334330049/5234000000000000000 : ℝ)+2*(429616564789/261700000000000 : ℝ)*(441/3125 : ℝ)=(10001505127854893/10000000000000000 : ℝ) by norm_num, show 1+2*(31049373537038073/100000000000000000000 : ℝ)=(50031049373537038073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5232362684334330049/5234000000000000000 : ℝ)*(X 1 0+X 2 0)+(429616564789/261700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (5232362684334330049/5234000000000000000 : ℝ)) (alpha := (429616564789/261700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5232362684334330049/5234000000000000000 : ℝ)*(X 0 1+X 2 1)+(429616564789/261700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (5232362684334330049/5234000000000000000 : ℝ)) (alpha := (429616564789/261700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5232362684334330049/5234000000000000000 : ℝ)*(X 0 2+X 1 2)+(429616564789/261700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (5232362684334330049/5234000000000000000 : ℝ)) (alpha := (429616564789/261700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056768251/5000000000 : ℝ)*X 0 0+(5390894777/10000000000 : ℝ)*X 0 1+(5267438297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344223223/10000000000 : ℝ)*X 1 0+(-10880639/50000000 : ℝ)*X 1 1+(1316859687/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068844689/2000000000 : ℝ)*X 2 0+(658429803/1250000000 : ℝ)*X 2 1+(-1088063967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174429517/5000000000 : ℝ)*X 0 0+(2112528429/5000000000 : ℝ)*X 0 1+(559521667/1250000000 : ℝ)*X 0 2+(2174429517/5000000000 : ℝ)*X 1 0+(2112528429/5000000000 : ℝ)*X 1 1+(559521667/1250000000 : ℝ)*X 1 2+(2174429517/5000000000 : ℝ)*X 2 0+(2112528429/5000000000 : ℝ)*X 2 1+(559521667/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2113540803/10000000000 : ℝ)*X 0 0+(5267749761/10000000000 : ℝ)*X 0 1+(269529121/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312693459/10000000000 : ℝ)*X 1 0+(-2052984151/10000000000 : ℝ)*X 1 1+(2695291039/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062538613/2000000000 : ℝ)*X 2 0+(1347645603/2500000000 : ℝ)*X 2 1+(-256623029/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087216997/2500000000 : ℝ)*X 0 0+(2237770103/5000000000 : ℝ)*X 0 1+(2112846363/5000000000 : ℝ)*X 0 2+(1087216997/2500000000 : ℝ)*X 1 0+(2237770103/5000000000 : ℝ)*X 1 1+(2112846363/5000000000 : ℝ)*X 1 2+(1087216997/2500000000 : ℝ)*X 2 0+(2237770103/5000000000 : ℝ)*X 2 1+(2112846363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161338776693374791559417637/65425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1168491971/100000000000000 : ℝ)*(base19) + (375130537/25000000000000 : ℝ)*(base23) + (143837599/50000000000000 : ℝ)*(upper3) + (2378453/100000000000000 : ℝ)*(upper4) + (61602137/50000000000000 : ℝ)*(upper5) + (1510297740587671/25000000000000 : ℝ)*(major0) + (1510297740587671/25000000000000 : ℝ)*(major1) + (1208238192470137/20000000000000 : ℝ)*(major2) + (8100076091886253/100000000000000 : ℝ)*(sp0) + (506257883415657/6250000000000 : ℝ)*(sp1) + (1620025160524067/20000000000000 : ℝ)*(sp2) + (3982232549242189/100000000000000 : ℝ)*(sp3) + (51211256231/100000000000000 : ℝ)*(sp4) + (10995058159/50000000000000 : ℝ)*(sp7) + (1991127269679253/50000000000000 : ℝ)*(f.failure) + (8100127303142483/100000000000000 : ℝ)*(f.sum) + (22249541618729/26170000000000000000000000000 : ℝ)*base66 + (1812780404759149121/130850000000000000000000000000000 : ℝ)*base68 + (807248542202510713/104680000000000000000000000000000 : ℝ)*base69 + (1069690856588450879/130850000000000000000000000000000 : ℝ)*base71 + (135733573435759/26170000000000000000000000000 : ℝ)*base74 + (1012377603751689287/104680000000000000000000000000000 : ℝ)*base76 + (963447319919644121/130850000000000000000000000000000 : ℝ)*base78 + (208998673990894121/130850000000000000000000000000000 : ℝ)*base80 + (4108471506853/6542500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2538901/5000000000000000000000 : ℝ)*base90 + (2538901/5000000000000000000000 : ℝ)*base92 + (52538901/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1066237685191396911761785173/261700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (922219317/100000000000000 : ℝ)*(base19) + (227160267/50000000000000 : ℝ)*(base23) + (15825189/6250000000000 : ℝ)*(lower1) + (45560567/50000000000000 : ℝ)*(lower4) + (9229299/25000000000000 : ℝ)*(upper5) + (6071792652660147/100000000000000 : ℝ)*(major0) + (6071792652660147/100000000000000 : ℝ)*(major1) + (6071792652660147/100000000000000 : ℝ)*(major2) + (14658667369/100000000000000 : ℝ)*(sp0) + (6006955803/100000000000000 : ℝ)*(sp1) + (254410744887611/3125000000000 : ℝ)*(sp4) + (8141151565895801/100000000000000 : ℝ)*(sp5) + (2035289510187597/25000000000000 : ℝ)*(sp6) + (4002426674440209/100000000000000 : ℝ)*(sp7) + (4002426674440209/100000000000000 : ℝ)*(f.failure) + (8141158495070921/100000000000000 : ℝ)*(f.sum) + (49532974699847/13085000000000000000000000000 : ℝ)*base66 + (6142124706073917203/523400000000000000000000000000000 : ℝ)*base67 + (3875760662398717203/523400000000000000000000000000000 : ℝ)*base69 + (483604187858517203/523400000000000000000000000000000 : ℝ)*base71 + (332860574943/3271250000000000000000000000 : ℝ)*base74 + (4273480446976117203/523400000000000000000000000000000 : ℝ)*base75 + (9722566518345717203/523400000000000000000000000000000 : ℝ)*base77 + (1240487332712517203/523400000000000000000000000000000 : ℝ)*base79 + (17149480276047/13085000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (27598353/10000000000000000000000 : ℝ)*base90 + (27598353/10000000000000000000000 : ℝ)*base92 + (27598353/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1256_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1256_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1256_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1256_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1256_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1437/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1256_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
