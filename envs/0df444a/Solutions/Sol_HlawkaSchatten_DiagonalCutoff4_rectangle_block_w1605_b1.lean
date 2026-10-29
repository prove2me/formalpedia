-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1605_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:48:44.076727+00:00
-- url     : https://prove2.me/submissions/78254278-6590-41b0-bc0e-7872f1b29be5

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
theorem support_rectangle_w1605_s3_0 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107300957/625000000 : ℝ)*x 0 + (1365411691/2500000000 : ℝ)*x 1 + (207189447/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107300957/625000000 : ℝ)^4739 ≤ (5281451853123/50000000000000 : ℝ)^3715 := by
    have hnat : (107300957 : ℕ)^4739*50000000000000^3715 ≤ 5281451853123^3715*625000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107300957 625000000 5281451853123 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365411691/2500000000 : ℝ)^4739 ≤ (9245910119951/20000000000000 : ℝ)^3715 := by
    have hnat : (1365411691 : ℕ)^4739*20000000000000^3715 ≤ 9245910119951^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365411691 2500000000 9245910119951 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207189447/400000000 : ℝ)^4739 ≤ (10801886419451/25000000000000 : ℝ)^3715 := by
    have hnat : (207189447 : ℕ)^4739*25000000000000^3715 ≤ 10801886419451^3715*400000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207189447 400000000 10801886419451 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107300957/625000000 : ℝ), (1365411691/2500000000 : ℝ), (207189447/400000000 : ℝ)] ![(5281451853123/50000000000000 : ℝ), (9245910119951/20000000000000 : ℝ), (10801886419451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107300957/625000000 : ℝ)|^4739 ≤ (5281451853123/50000000000000 : ℝ)^3715
        have hw : |(-107300957/625000000 : ℝ)|=(107300957/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365411691/2500000000 : ℝ)|^4739 ≤ (9245910119951/20000000000000 : ℝ)^3715
        have hw : |(1365411691/2500000000 : ℝ)|=(1365411691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207189447/400000000 : ℝ)|^4739 ≤ (10801886419451/25000000000000 : ℝ)^3715
        have hw : |(207189447/400000000 : ℝ)|=(207189447/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s3_1 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677221903/5000000000 : ℝ)*x 0 + (-1862233737/10000000000 : ℝ)*x 1 + (5179736193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677221903/5000000000 : ℝ)^4739 ≤ (45075170955099/100000000000000 : ℝ)^3715 := by
    have hnat : (2677221903 : ℕ)^4739*100000000000000^3715 ≤ 45075170955099^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677221903 5000000000 45075170955099 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862233737/10000000000 : ℝ)^4739 ≤ (468691326513/4000000000000 : ℝ)^3715 := by
    have hnat : (1862233737 : ℕ)^4739*4000000000000^3715 ≤ 468691326513^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862233737 10000000000 468691326513 4000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179736193/10000000000 : ℝ)^4739 ≤ (43207545869341/100000000000000 : ℝ)^3715 := by
    have hnat : (5179736193 : ℕ)^4739*100000000000000^3715 ≤ 43207545869341^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179736193 10000000000 43207545869341 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677221903/5000000000 : ℝ), (-1862233737/10000000000 : ℝ), (5179736193/10000000000 : ℝ)] ![(45075170955099/100000000000000 : ℝ), (468691326513/4000000000000 : ℝ), (43207545869341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677221903/5000000000 : ℝ)|^4739 ≤ (45075170955099/100000000000000 : ℝ)^3715
        have hw : |(2677221903/5000000000 : ℝ)|=(2677221903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1862233737/10000000000 : ℝ)|^4739 ≤ (468691326513/4000000000000 : ℝ)^3715
        have hw : |(-1862233737/10000000000 : ℝ)|=(1862233737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179736193/10000000000 : ℝ)|^4739 ≤ (43207545869341/100000000000000 : ℝ)^3715
        have hw : |(5179736193/10000000000 : ℝ)|=(5179736193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s3_2 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677221913/5000000000 : ℝ)*x 0 + (5179736171/10000000000 : ℝ)*x 1 + (-1862233739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677221913/5000000000 : ℝ)^4739 ≤ (45075171169873/100000000000000 : ℝ)^3715 := by
    have hnat : (2677221913 : ℕ)^4739*100000000000000^3715 ≤ 45075171169873^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677221913 5000000000 45075171169873 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179736171/10000000000 : ℝ)^4739 ≤ (1080188640881/2500000000000 : ℝ)^3715 := by
    have hnat : (5179736171 : ℕ)^4739*2500000000000^3715 ≤ 1080188640881^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179736171 10000000000 1080188640881 2500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1862233739/10000000000 : ℝ)^4739 ≤ (11717283178877/100000000000000 : ℝ)^3715 := by
    have hnat : (1862233739 : ℕ)^4739*100000000000000^3715 ≤ 11717283178877^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862233739 10000000000 11717283178877 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677221913/5000000000 : ℝ), (5179736171/10000000000 : ℝ), (-1862233739/10000000000 : ℝ)] ![(45075171169873/100000000000000 : ℝ), (1080188640881/2500000000000 : ℝ), (11717283178877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677221913/5000000000 : ℝ)|^4739 ≤ (45075171169873/100000000000000 : ℝ)^3715
        have hw : |(2677221913/5000000000 : ℝ)|=(2677221913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179736171/10000000000 : ℝ)|^4739 ≤ (1080188640881/2500000000000 : ℝ)^3715
        have hw : |(5179736171/10000000000 : ℝ)|=(5179736171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1862233739/10000000000 : ℝ)|^4739 ≤ (11717283178877/100000000000000 : ℝ)^3715
        have hw : |(-1862233739/10000000000 : ℝ)|=(1862233739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s3_3 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527075119/1250000000 : ℝ)*x 0 + (3883400253/10000000000 : ℝ)*x 1 + (91431843/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527075119/1250000000 : ℝ)^4739 ≤ (33234368358667/100000000000000 : ℝ)^3715 := by
    have hnat : (527075119 : ℕ)^4739*100000000000000^3715 ≤ 33234368358667^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527075119 1250000000 33234368358667 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3883400253/10000000000 : ℝ)^4739 ≤ (14960733427653/50000000000000 : ℝ)^3715 := by
    have hnat : (3883400253 : ℕ)^4739*50000000000000^3715 ≤ 14960733427653^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3883400253 10000000000 14960733427653 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91431843/200000000 : ℝ)^4739 ≤ (18422082389137/50000000000000 : ℝ)^3715 := by
    have hnat : (91431843 : ℕ)^4739*50000000000000^3715 ≤ 18422082389137^3715*200000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91431843 200000000 18422082389137 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527075119/1250000000 : ℝ), (3883400253/10000000000 : ℝ), (91431843/200000000 : ℝ)] ![(33234368358667/100000000000000 : ℝ), (14960733427653/50000000000000 : ℝ), (18422082389137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527075119/1250000000 : ℝ)|^4739 ≤ (33234368358667/100000000000000 : ℝ)^3715
        have hw : |(527075119/1250000000 : ℝ)|=(527075119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3883400253/10000000000 : ℝ)|^4739 ≤ (14960733427653/50000000000000 : ℝ)^3715
        have hw : |(3883400253/10000000000 : ℝ)|=(3883400253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91431843/200000000 : ℝ)|^4739 ≤ (18422082389137/50000000000000 : ℝ)^3715
        have hw : |(91431843/200000000 : ℝ)|=(91431843/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s3_4 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1716887561/10000000000 : ℝ)*x 0 + (5181835319/10000000000 : ℝ)*x 1 + (1364881329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1716887561/10000000000 : ℝ)^4739 ≤ (10563470757079/100000000000000 : ℝ)^3715 := by
    have hnat : (1716887561 : ℕ)^4739*100000000000000^3715 ≤ 10563470757079^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716887561 10000000000 10563470757079 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181835319/10000000000 : ℝ)^4739 ≤ (10807470945777/25000000000000 : ℝ)^3715 := by
    have hnat : (5181835319 : ℕ)^4739*25000000000000^3715 ≤ 10807470945777^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181835319 10000000000 10807470945777 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364881329/2500000000 : ℝ)^4739 ≤ (23103322726121/50000000000000 : ℝ)^3715 := by
    have hnat : (1364881329 : ℕ)^4739*50000000000000^3715 ≤ 23103322726121^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364881329 2500000000 23103322726121 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1716887561/10000000000 : ℝ), (5181835319/10000000000 : ℝ), (1364881329/2500000000 : ℝ)] ![(10563470757079/100000000000000 : ℝ), (10807470945777/25000000000000 : ℝ), (23103322726121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1716887561/10000000000 : ℝ)|^4739 ≤ (10563470757079/100000000000000 : ℝ)^3715
        have hw : |(-1716887561/10000000000 : ℝ)|=(1716887561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181835319/10000000000 : ℝ)|^4739 ≤ (10807470945777/25000000000000 : ℝ)^3715
        have hw : |(5181835319/10000000000 : ℝ)|=(5181835319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364881329/2500000000 : ℝ)|^4739 ≤ (23103322726121/50000000000000 : ℝ)^3715
        have hw : |(1364881329/2500000000 : ℝ)|=(1364881329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s3_5 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131991091/250000000 : ℝ)*x 0 + (-316488931/2000000000 : ℝ)*x 1 + (5459524873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131991091/250000000 : ℝ)^4739 ≤ (22136733827/50000000000 : ℝ)^3715 := by
    have hnat : (131991091 : ℕ)^4739*50000000000^3715 ≤ 22136733827^3715*250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131991091 250000000 22136733827 50000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316488931/2000000000 : ℝ)^4739 ≤ (9519891662537/100000000000000 : ℝ)^3715 := by
    have hnat : (316488931 : ℕ)^4739*100000000000000^3715 ≤ 9519891662537^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316488931 2000000000 9519891662537 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459524873/10000000000 : ℝ)^4739 ≤ (46206640669453/100000000000000 : ℝ)^3715 := by
    have hnat : (5459524873 : ℕ)^4739*100000000000000^3715 ≤ 46206640669453^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459524873 10000000000 46206640669453 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131991091/250000000 : ℝ), (-316488931/2000000000 : ℝ), (5459524873/10000000000 : ℝ)] ![(22136733827/50000000000 : ℝ), (9519891662537/100000000000000 : ℝ), (46206640669453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131991091/250000000 : ℝ)|^4739 ≤ (22136733827/50000000000 : ℝ)^3715
        have hw : |(131991091/250000000 : ℝ)|=(131991091/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-316488931/2000000000 : ℝ)|^4739 ≤ (9519891662537/100000000000000 : ℝ)^3715
        have hw : |(-316488931/2000000000 : ℝ)|=(316488931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459524873/10000000000 : ℝ)|^4739 ≤ (46206640669453/100000000000000 : ℝ)^3715
        have hw : |(5459524873/10000000000 : ℝ)|=(5459524873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s3_6 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527964281/1000000000 : ℝ)*x 0 + (1364881349/2500000000 : ℝ)*x 1 + (-395611269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527964281/1000000000 : ℝ)^4739 ≤ (1383545586731/3125000000000 : ℝ)^3715 := by
    have hnat : (527964281 : ℕ)^4739*3125000000000^3715 ≤ 1383545586731^3715*1000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527964281 1000000000 1383545586731 3125000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364881349/2500000000 : ℝ)^4739 ≤ (46206646315951/100000000000000 : ℝ)^3715 := by
    have hnat : (1364881349 : ℕ)^4739*100000000000000^3715 ≤ 46206646315951^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364881349 2500000000 46206646315951 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395611269/2500000000 : ℝ)^4739 ≤ (9519894893363/100000000000000 : ℝ)^3715 := by
    have hnat : (395611269 : ℕ)^4739*100000000000000^3715 ≤ 9519894893363^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395611269 2500000000 9519894893363 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527964281/1000000000 : ℝ), (1364881349/2500000000 : ℝ), (-395611269/2500000000 : ℝ)] ![(1383545586731/3125000000000 : ℝ), (46206646315951/100000000000000 : ℝ), (9519894893363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527964281/1000000000 : ℝ)|^4739 ≤ (1383545586731/3125000000000 : ℝ)^3715
        have hw : |(527964281/1000000000 : ℝ)|=(527964281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364881349/2500000000 : ℝ)|^4739 ≤ (46206646315951/100000000000000 : ℝ)^3715
        have hw : |(1364881349/2500000000 : ℝ)|=(1364881349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395611269/2500000000 : ℝ)|^4739 ≤ (9519894893363/100000000000000 : ℝ)^3715
        have hw : |(-395611269/2500000000 : ℝ)|=(395611269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s3_7 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4216777031/10000000000 : ℝ)*x 0 + (4566466713/10000000000 : ℝ)*x 1 + (3888579543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216777031/10000000000 : ℝ)^4739 ≤ (33236138723931/100000000000000 : ℝ)^3715 := by
    have hnat : (4216777031 : ℕ)^4739*100000000000000^3715 ≤ 33236138723931^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216777031 10000000000 33236138723931 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4566466713/10000000000 : ℝ)^4739 ≤ (9197869765191/25000000000000 : ℝ)^3715 := by
    have hnat : (4566466713 : ℕ)^4739*25000000000000^3715 ≤ 9197869765191^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566466713 10000000000 9197869765191 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3888579543/10000000000 : ℝ)^4739 ≤ (1198895287773/4000000000000 : ℝ)^3715 := by
    have hnat : (3888579543 : ℕ)^4739*4000000000000^3715 ≤ 1198895287773^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888579543 10000000000 1198895287773 4000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216777031/10000000000 : ℝ), (4566466713/10000000000 : ℝ), (3888579543/10000000000 : ℝ)] ![(33236138723931/100000000000000 : ℝ), (9197869765191/25000000000000 : ℝ), (1198895287773/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216777031/10000000000 : ℝ)|^4739 ≤ (33236138723931/100000000000000 : ℝ)^3715
        have hw : |(4216777031/10000000000 : ℝ)|=(4216777031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4566466713/10000000000 : ℝ)|^4739 ≤ (9197869765191/25000000000000 : ℝ)^3715
        have hw : |(4566466713/10000000000 : ℝ)|=(4566466713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3888579543/10000000000 : ℝ)|^4739 ≤ (1198895287773/4000000000000 : ℝ)^3715
        have hw : |(3888579543/10000000000 : ℝ)|=(3888579543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1605_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3303/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4091/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3303/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3303/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3303/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3303/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3303/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3303/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10253/100000 : ℝ) ^ (4735/1024 : ℝ) ≤ (2667790020982923/100000000000000000000 : ℝ) := by
    have hpowers : (10253/100000 : ℝ)^4735 ≤ (2667790020982923/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10253 : ℕ)^4735*100000000000000000000^1024 ≤ 2667790020982923^1024*100000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10253 100000 2667790020982923 100000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10253/100000 : ℝ)) (X := (2667790020982923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3303/20000 : ℝ) ^ (4735/1024 : ℝ) ≤ (24179772690773119/100000000000000000000 : ℝ) := by
    have hpowers : (3303/20000 : ℝ)^4735 ≤ (24179772690773119/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3303 : ℕ)^4735*100000000000000000000^1024 ≤ 24179772690773119^1024*20000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3303 20000 24179772690773119 100000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3303/20000 : ℝ)) (X := (24179772690773119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002667790020982923/50000000000000000000 : ℝ) ≤ (10000115385844357/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (50002667790020982923/50000000000000000000 : ℝ)^1024 ≤ (10000115385844357/10000000000000000 : ℝ)^4735 := by
      have hnat : (50002667790020982923 : ℕ)^1024*10000000000000000^4735 ≤ 10000115385844357^4735*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002667790020982923 50000000000000000000 10000115385844357 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000115385844357/10000000000000000 : ℝ)) (X := (50002667790020982923/50000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013423781355878021/50000000000000000000 : ℝ) ≤ (1250072568670353/1250000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (50013423781355878021/50000000000000000000 : ℝ)^1024 ≤ (1250072568670353/1250000000000000 : ℝ)^4735 := by
      have hnat : (50013423781355878021 : ℕ)^1024*1250000000000000^4735 ≤ 1250072568670353^4735*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013423781355878021 50000000000000000000 1250072568670353 1250000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250072568670353/1250000000000000 : ℝ)) (X := (50013423781355878021/50000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024179772690773119/50000000000000000000 : ℝ) ≤ (10001045712881291/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (50024179772690773119/50000000000000000000 : ℝ)^1024 ≤ (10001045712881291/10000000000000000 : ℝ)^4735 := by
      have hnat : (50024179772690773119 : ℕ)^1024*10000000000000000^4735 ≤ 10001045712881291^4735*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024179772690773119 50000000000000000000 10001045712881291 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001045712881291/10000000000000000 : ℝ)) (X := (50024179772690773119/50000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2667790020982923/100000000000000000000 : ℝ) ≤ ((244574937121279997/244609375000000000 : ℝ)+2*(465163518467/626200000000000 : ℝ)*(10253/100000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (244574937121279997/244609375000000000 : ℝ)+2*(465163518467/626200000000000 : ℝ)*(10253/100000 : ℝ)=(10000115385844357/10000000000000000 : ℝ) by norm_num, show 1+2*(2667790020982923/100000000000000000000 : ℝ)=(50002667790020982923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24179772690773119/100000000000000000000 : ℝ)+(2667790020982923/100000000000000000000 : ℝ) ≤ ((244574937121279997/244609375000000000 : ℝ)+(465163518467/626200000000000 : ℝ)*((3303/20000 : ℝ)+(10253/100000 : ℝ)))^(4735/1024 : ℝ) := by
    rw [show (244574937121279997/244609375000000000 : ℝ)+(465163518467/626200000000000 : ℝ)*((3303/20000 : ℝ)+(10253/100000 : ℝ))=(1250072568670353/1250000000000000 : ℝ) by norm_num, show 1+(24179772690773119/100000000000000000000 : ℝ)+(2667790020982923/100000000000000000000 : ℝ)=(50013423781355878021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24179772690773119/100000000000000000000 : ℝ) ≤ ((244574937121279997/244609375000000000 : ℝ)+2*(465163518467/626200000000000 : ℝ)*(3303/20000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (244574937121279997/244609375000000000 : ℝ)+2*(465163518467/626200000000000 : ℝ)*(3303/20000 : ℝ)=(10001045712881291/10000000000000000 : ℝ) by norm_num, show 1+2*(24179772690773119/100000000000000000000 : ℝ)=(50024179772690773119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (244574937121279997/244609375000000000 : ℝ)*(X 1 0+X 2 0)+(465163518467/626200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10253/100000 : ℝ)) (hi := (3303/20000 : ℝ)) (c := (244574937121279997/244609375000000000 : ℝ)) (alpha := (465163518467/626200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (244574937121279997/244609375000000000 : ℝ)*(X 0 1+X 2 1)+(465163518467/626200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10253/100000 : ℝ)) (hi := (3303/20000 : ℝ)) (c := (244574937121279997/244609375000000000 : ℝ)) (alpha := (465163518467/626200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (244574937121279997/244609375000000000 : ℝ)*(X 0 2+X 1 2)+(465163518467/626200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10253/100000 : ℝ)) (hi := (3303/20000 : ℝ)) (c := (244574937121279997/244609375000000000 : ℝ)) (alpha := (465163518467/626200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107300957/625000000 : ℝ)*X 0 0+(1365411691/2500000000 : ℝ)*X 0 1+(207189447/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677221903/5000000000 : ℝ)*X 1 0+(-1862233737/10000000000 : ℝ)*X 1 1+(5179736193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677221913/5000000000 : ℝ)*X 2 0+(5179736171/10000000000 : ℝ)*X 2 1+(-1862233739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((527075119/1250000000 : ℝ)*X 0 0+(3883400253/10000000000 : ℝ)*X 0 1+(91431843/200000000 : ℝ)*X 0 2+(527075119/1250000000 : ℝ)*X 1 0+(3883400253/10000000000 : ℝ)*X 1 1+(91431843/200000000 : ℝ)*X 1 2+(527075119/1250000000 : ℝ)*X 2 0+(3883400253/10000000000 : ℝ)*X 2 1+(91431843/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1716887561/10000000000 : ℝ)*X 0 0+(5181835319/10000000000 : ℝ)*X 0 1+(1364881329/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((131991091/250000000 : ℝ)*X 1 0+(-316488931/2000000000 : ℝ)*X 1 1+(5459524873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527964281/1000000000 : ℝ)*X 2 0+(1364881349/2500000000 : ℝ)*X 2 1+(-395611269/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216777031/10000000000 : ℝ)*X 0 0+(4566466713/10000000000 : ℝ)*X 0 1+(3888579543/10000000000 : ℝ)*X 0 2+(4216777031/10000000000 : ℝ)*X 1 0+(4566466713/10000000000 : ℝ)*X 1 1+(3888579543/10000000000 : ℝ)*X 1 2+(4216777031/10000000000 : ℝ)*X 2 0+(4566466713/10000000000 : ℝ)*X 2 1+(3888579543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (562238677387631062438035849/97843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (467681827/50000000000000 : ℝ)*(base19) + (179380689/20000000000000 : ℝ)*(base23) + (13843897/50000000000000 : ℝ)*(lower2) + (35685979/25000000000000 : ℝ)*(upper3) + (26290403/25000000000000 : ℝ)*(upper5) + (2500169781462429/100000000000000 : ℝ)*(major0) + (2500169781462429/100000000000000 : ℝ)*(major1) + (2500169781462429/100000000000000 : ℝ)*(major2) + (6928194230511/195312500000 : ℝ)*(sp0) + (177362287583099/5000000000000 : ℝ)*(sp1) + (354724579012219/10000000000000 : ℝ)*(sp2) + (1453087627496211/100000000000000 : ℝ)*(sp3) + (11241004003/100000000000000 : ℝ)*(sp4) + (2528429981/50000000000000 : ℝ)*(sp7) + (363273171089043/25000000000000 : ℝ)*(f.failure) + (1773623343512817/50000000000000 : ℝ)*(f.sum) + (132465307307027/31310000000000000000000000000 : ℝ)*base66 + (504575856298191421/195687500000000000000000000000000 : ℝ)*base68 + (2429340782083816421/195687500000000000000000000000000 : ℝ)*base70 + (406417070146808579/195687500000000000000000000000000 : ℝ)*base71 + (82578748498353/31310000000000000000000000000 : ℝ)*base73 + (270763746930816421/195687500000000000000000000000000 : ℝ)*base76 + (1357588928656941421/195687500000000000000000000000000 : ℝ)*base78 + (1522180930531628921/195687500000000000000000000000000 : ℝ)*base80 + (102387129717517/31310000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (27114597/2500000000000000000000 : ℝ)*base90 + (27114597/2500000000000000000000 : ℝ)*base92 + (27114597/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (341743023167492328614246961/48921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396797727/25000000000000 : ℝ)*(base19) + (451264327/50000000000000 : ℝ)*(base23) + (8546271/100000000000000 : ℝ)*(upper2) + (58330763/50000000000000 : ℝ)*(upper3) + (294208757/100000000000000 : ℝ)*(upper5) + (317269292070603/12500000000000 : ℝ)*(major0) + (317269292070603/12500000000000 : ℝ)*(major1) + (317269292070603/12500000000000 : ℝ)*(major2) + (3177169927/20000000000000 : ℝ)*(sp1) + (6376565419/100000000000000 : ℝ)*(sp2) + (3601139223543229/100000000000000 : ℝ)*(sp4) + (1800560875251343/50000000000000 : ℝ)*(sp5) + (900282986112289/25000000000000 : ℝ)*(sp6) + (1475169216736917/100000000000000 : ℝ)*(sp7) + (1475169216736917/100000000000000 : ℝ)*(f.failure) + (3601139223543229/100000000000000 : ℝ)*(f.sum) + (13027195107457/7827500000000000000000000000 : ℝ)*base65 + (2800803998658847/24460937500000000000000000000000 : ℝ)*base68 + (47220690800645819/48921875000000000000000000000000 : ℝ)*base70 + (47110127001822931/48921875000000000000000000000000 : ℝ)*base71 + (8199306279381/3913750000000000000000000000 : ℝ)*base73 + (108973221720940097/24460937500000000000000000000000 : ℝ)*base76 + (16793553968635431/48921875000000000000000000000000 : ℝ)*base77 + (34941424694965493/6115234375000000000000000000000 : ℝ)*base80 + (14181105776567/7827500000000000000000000000 : ℝ)*base81 + (14880243/10000000000000000000000 : ℝ)*base90 + (14880243/10000000000000000000000 : ℝ)*base92 + (14880243/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1605_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3303/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1605_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1605_s4_0 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85847279/500000000 : ℝ)*x 0 + (546099427/1000000000 : ℝ)*x 1 + (647537771/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85847279/500000000 : ℝ)^4739 ≤ (10563926127621/100000000000000 : ℝ)^3715 := by
    have hnat : (85847279 : ℕ)^4739*100000000000000^3715 ≤ 10563926127621^3715*500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85847279 500000000 10563926127621 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546099427/1000000000 : ℝ)^4739 ≤ (11555626349943/25000000000000 : ℝ)^3715 := by
    have hnat : (546099427 : ℕ)^4739*25000000000000^3715 ≤ 11555626349943^3715*1000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546099427 1000000000 11555626349943 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647537771/1250000000 : ℝ)^4739 ≤ (43213568464031/100000000000000 : ℝ)^3715 := by
    have hnat : (647537771 : ℕ)^4739*100000000000000^3715 ≤ 43213568464031^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647537771 1250000000 43213568464031 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85847279/500000000 : ℝ), (546099427/1000000000 : ℝ), (647537771/1250000000 : ℝ)] ![(10563926127621/100000000000000 : ℝ), (11555626349943/25000000000000 : ℝ), (43213568464031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85847279/500000000 : ℝ)|^4739 ≤ (10563926127621/100000000000000 : ℝ)^3715
        have hw : |(-85847279/500000000 : ℝ)|=(85847279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546099427/1000000000 : ℝ)|^4739 ≤ (11555626349943/25000000000000 : ℝ)^3715
        have hw : |(546099427/1000000000 : ℝ)|=(546099427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647537771/1250000000 : ℝ)|^4739 ≤ (43213568464031/100000000000000 : ℝ)^3715
        have hw : |(647537771/1250000000 : ℝ)|=(647537771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s4_1 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677134903/5000000000 : ℝ)*x 0 + (-1861716189/10000000000 : ℝ)*x 1 + (103606043/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677134903/5000000000 : ℝ)^4739 ≤ (22536651216559/50000000000000 : ℝ)^3715 := by
    have hnat : (2677134903 : ℕ)^4739*50000000000000^3715 ≤ 22536651216559^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677134903 5000000000 22536651216559 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1861716189/10000000000 : ℝ)^4739 ≤ (11713129276339/100000000000000 : ℝ)^3715 := by
    have hnat : (1861716189 : ℕ)^4739*100000000000000^3715 ≤ 11713129276339^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861716189 10000000000 11713129276339 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103606043/200000000 : ℝ)^4739 ≤ (5401696034061/12500000000000 : ℝ)^3715 := by
    have hnat : (103606043 : ℕ)^4739*12500000000000^3715 ≤ 5401696034061^3715*200000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103606043 200000000 5401696034061 12500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677134903/5000000000 : ℝ), (-1861716189/10000000000 : ℝ), (103606043/200000000 : ℝ)] ![(22536651216559/50000000000000 : ℝ), (11713129276339/100000000000000 : ℝ), (5401696034061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677134903/5000000000 : ℝ)|^4739 ≤ (22536651216559/50000000000000 : ℝ)^3715
        have hw : |(2677134903/5000000000 : ℝ)|=(2677134903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1861716189/10000000000 : ℝ)|^4739 ≤ (11713129276339/100000000000000 : ℝ)^3715
        have hw : |(-1861716189/10000000000 : ℝ)|=(1861716189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103606043/200000000 : ℝ)|^4739 ≤ (5401696034061/12500000000000 : ℝ)^3715
        have hw : |(103606043/200000000 : ℝ)|=(103606043/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s4_2 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354269723/10000000000 : ℝ)*x 0 + (5180302287/10000000000 : ℝ)*x 1 + (-1861716119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354269723/10000000000 : ℝ)^4739 ≤ (5634162692727/12500000000000 : ℝ)^3715 := by
    have hnat : (5354269723 : ℕ)^4739*12500000000000^3715 ≤ 5634162692727^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354269723 10000000000 5634162692727 12500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180302287/10000000000 : ℝ)^4739 ≤ (2160678486517/5000000000000 : ℝ)^3715 := by
    have hnat : (5180302287 : ℕ)^4739*5000000000000^3715 ≤ 2160678486517^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180302287 10000000000 2160678486517 5000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1861716119/10000000000 : ℝ)^4739 ≤ (5856564357267/50000000000000 : ℝ)^3715 := by
    have hnat : (1861716119 : ℕ)^4739*50000000000000^3715 ≤ 5856564357267^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861716119 10000000000 5856564357267 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354269723/10000000000 : ℝ), (5180302287/10000000000 : ℝ), (-1861716119/10000000000 : ℝ)] ![(5634162692727/12500000000000 : ℝ), (2160678486517/5000000000000 : ℝ), (5856564357267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354269723/10000000000 : ℝ)|^4739 ≤ (5634162692727/12500000000000 : ℝ)^3715
        have hw : |(5354269723/10000000000 : ℝ)|=(5354269723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180302287/10000000000 : ℝ)|^4739 ≤ (2160678486517/5000000000000 : ℝ)^3715
        have hw : |(5180302287/10000000000 : ℝ)|=(5180302287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1861716119/10000000000 : ℝ)|^4739 ≤ (5856564357267/50000000000000 : ℝ)^3715
        have hw : |(-1861716119/10000000000 : ℝ)|=(1861716119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s4_3 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4216685861/10000000000 : ℝ)*x 0 + (3884878433/10000000000 : ℝ)*x 1 + (285630987/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216685861/10000000000 : ℝ)^4739 ≤ (33235222063517/100000000000000 : ℝ)^3715 := by
    have hnat : (4216685861 : ℕ)^4739*100000000000000^3715 ≤ 33235222063517^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216685861 10000000000 33235222063517 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3884878433/10000000000 : ℝ)^4739 ≤ (7483999072511/25000000000000 : ℝ)^3715 := by
    have hnat : (3884878433 : ℕ)^4739*25000000000000^3715 ≤ 7483999072511^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3884878433 10000000000 7483999072511 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285630987/625000000 : ℝ)^4739 ≤ (36828781636423/100000000000000 : ℝ)^3715 := by
    have hnat : (285630987 : ℕ)^4739*100000000000000^3715 ≤ 36828781636423^3715*625000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285630987 625000000 36828781636423 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216685861/10000000000 : ℝ), (3884878433/10000000000 : ℝ), (285630987/625000000 : ℝ)] ![(33235222063517/100000000000000 : ℝ), (7483999072511/25000000000000 : ℝ), (36828781636423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216685861/10000000000 : ℝ)|^4739 ≤ (33235222063517/100000000000000 : ℝ)^3715
        have hw : |(4216685861/10000000000 : ℝ)|=(4216685861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3884878433/10000000000 : ℝ)|^4739 ≤ (7483999072511/25000000000000 : ℝ)^3715
        have hw : |(3884878433/10000000000 : ℝ)|=(3884878433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285630987/625000000 : ℝ)|^4739 ≤ (36828781636423/100000000000000 : ℝ)^3715
        have hw : |(285630987/625000000 : ℝ)|=(285630987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s4_4 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-34340329/200000000 : ℝ)*x 0 + (2591191973/5000000000 : ℝ)*x 1 + (5458890809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34340329/200000000 : ℝ)^4739 ≤ (1320560295857/12500000000000 : ℝ)^3715 := by
    have hnat : (34340329 : ℕ)^4739*12500000000000^3715 ≤ 1320560295857^3715*200000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34340329 200000000 1320560295857 12500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591191973/5000000000 : ℝ)^4739 ≤ (540446530317/1250000000000 : ℝ)^3715 := by
    have hnat : (2591191973 : ℕ)^4739*1250000000000^3715 ≤ 540446530317^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591191973 5000000000 540446530317 1250000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458890809/10000000000 : ℝ)^4739 ≤ (23099897597283/50000000000000 : ℝ)^3715 := by
    have hnat : (5458890809 : ℕ)^4739*50000000000000^3715 ≤ 23099897597283^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458890809 10000000000 23099897597283 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34340329/200000000 : ℝ), (2591191973/5000000000 : ℝ), (5458890809/10000000000 : ℝ)] ![(1320560295857/12500000000000 : ℝ), (540446530317/1250000000000 : ℝ), (23099897597283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34340329/200000000 : ℝ)|^4739 ≤ (1320560295857/12500000000000 : ℝ)^3715
        have hw : |(-34340329/200000000 : ℝ)|=(34340329/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591191973/5000000000 : ℝ)|^4739 ≤ (540446530317/1250000000000 : ℝ)^3715
        have hw : |(2591191973/5000000000 : ℝ)|=(2591191973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458890809/10000000000 : ℝ)|^4739 ≤ (23099897597283/50000000000000 : ℝ)^3715
        have hw : |(5458890809/10000000000 : ℝ)|=(5458890809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s4_5 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055958677/2000000000 : ℝ)*x 0 + (-1583127137/10000000000 : ℝ)*x 1 + (109177827/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055958677/2000000000 : ℝ)^4739 ≤ (22137534750159/50000000000000 : ℝ)^3715 := by
    have hnat : (1055958677 : ℕ)^4739*50000000000000^3715 ≤ 22137534750159^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055958677 2000000000 22137534750159 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1583127137/10000000000 : ℝ)^4739 ≤ (238128236403/2500000000000 : ℝ)^3715 := by
    have hnat : (1583127137 : ℕ)^4739*2500000000000^3715 ≤ 238128236403^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583127137 10000000000 238128236403 2500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109177827/200000000 : ℝ)^4739 ≤ (46199801035211/100000000000000 : ℝ)^3715 := by
    have hnat : (109177827 : ℕ)^4739*100000000000000^3715 ≤ 46199801035211^3715*200000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109177827 200000000 46199801035211 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055958677/2000000000 : ℝ), (-1583127137/10000000000 : ℝ), (109177827/200000000 : ℝ)] ![(22137534750159/50000000000000 : ℝ), (238128236403/2500000000000 : ℝ), (46199801035211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055958677/2000000000 : ℝ)|^4739 ≤ (22137534750159/50000000000000 : ℝ)^3715
        have hw : |(1055958677/2000000000 : ℝ)|=(1055958677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1583127137/10000000000 : ℝ)|^4739 ≤ (238128236403/2500000000000 : ℝ)^3715
        have hw : |(-1583127137/10000000000 : ℝ)|=(1583127137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109177827/200000000 : ℝ)|^4739 ≤ (46199801035211/100000000000000 : ℝ)^3715
        have hw : |(109177827/200000000 : ℝ)|=(109177827/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s4_6 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279793827/10000000000 : ℝ)*x 0 + (5458890721/10000000000 : ℝ)*x 1 + (-316625481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279793827/10000000000 : ℝ)^4739 ≤ (44275074228481/100000000000000 : ℝ)^3715 := by
    have hnat : (5279793827 : ℕ)^4739*100000000000000^3715 ≤ 44275074228481^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279793827 10000000000 44275074228481 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458890721/10000000000 : ℝ)^4739 ≤ (46199794244517/100000000000000 : ℝ)^3715 := by
    have hnat : (5458890721 : ℕ)^4739*100000000000000^3715 ≤ 46199794244517^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458890721 10000000000 46199794244517 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316625481/2000000000 : ℝ)^4739 ≤ (4762565756521/50000000000000 : ℝ)^3715 := by
    have hnat : (316625481 : ℕ)^4739*50000000000000^3715 ≤ 4762565756521^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316625481 2000000000 4762565756521 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279793827/10000000000 : ℝ), (5458890721/10000000000 : ℝ), (-316625481/2000000000 : ℝ)] ![(44275074228481/100000000000000 : ℝ), (46199794244517/100000000000000 : ℝ), (4762565756521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279793827/10000000000 : ℝ)|^4739 ≤ (44275074228481/100000000000000 : ℝ)^3715
        have hw : |(5279793827/10000000000 : ℝ)|=(5279793827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458890721/10000000000 : ℝ)|^4739 ≤ (46199794244517/100000000000000 : ℝ)^3715
        have hw : |(5458890721/10000000000 : ℝ)|=(5458890721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-316625481/2000000000 : ℝ)|^4739 ≤ (4762565756521/50000000000000 : ℝ)^3715
        have hw : |(-316625481/2000000000 : ℝ)|=(316625481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s4_7 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4216859239/10000000000 : ℝ)*x 0 + (4565014409/10000000000 : ℝ)*x 1 + (1945006709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216859239/10000000000 : ℝ)^4739 ≤ (1661848264071/5000000000000 : ℝ)^3715 := by
    have hnat : (4216859239 : ℕ)^4739*5000000000000^3715 ≤ 1661848264071^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216859239 10000000000 1661848264071 5000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4565014409/10000000000 : ℝ)^4739 ≤ (18388276703937/50000000000000 : ℝ)^3715 := by
    have hnat : (4565014409 : ℕ)^4739*50000000000000^3715 ≤ 18388276703937^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565014409 10000000000 18388276703937 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945006709/5000000000 : ℝ)^4739 ≤ (29986481298723/100000000000000 : ℝ)^3715 := by
    have hnat : (1945006709 : ℕ)^4739*100000000000000^3715 ≤ 29986481298723^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945006709 5000000000 29986481298723 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216859239/10000000000 : ℝ), (4565014409/10000000000 : ℝ), (1945006709/5000000000 : ℝ)] ![(1661848264071/5000000000000 : ℝ), (18388276703937/50000000000000 : ℝ), (29986481298723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216859239/10000000000 : ℝ)|^4739 ≤ (1661848264071/5000000000000 : ℝ)^3715
        have hw : |(4216859239/10000000000 : ℝ)|=(4216859239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4565014409/10000000000 : ℝ)|^4739 ≤ (18388276703937/50000000000000 : ℝ)^3715
        have hw : |(4565014409/10000000000 : ℝ)|=(4565014409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1945006709/5000000000 : ℝ)|^4739 ≤ (29986481298723/100000000000000 : ℝ)^3715
        have hw : |(1945006709/5000000000 : ℝ)|=(1945006709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1605_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10401/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (327/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10389/100000 : ℝ) ^ (4735/1024 : ℝ) ≤ (2835397510404213/100000000000000000000 : ℝ) := by
    have hpowers : (10389/100000 : ℝ)^4735 ≤ (2835397510404213/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10389 : ℕ)^4735*100000000000000000000^1024 ≤ 2835397510404213^1024*100000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10389 100000 2835397510404213 100000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10389/100000 : ℝ)) (X := (2835397510404213/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4091/25000 : ℝ) ^ (4735/1024 : ℝ) ≤ (2317429273575353/10000000000000000000 : ℝ) := by
    have hpowers : (4091/25000 : ℝ)^4735 ≤ (2317429273575353/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4091 : ℕ)^4735*10000000000000000000^1024 ≤ 2317429273575353^1024*25000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4091 25000 2317429273575353 10000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4091/25000 : ℝ)) (X := (2317429273575353/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002835397510404213/50000000000000000000 : ℝ) ≤ (10000122634953841/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (50002835397510404213/50000000000000000000 : ℝ)^1024 ≤ (10000122634953841/10000000000000000 : ℝ)^4735 := by
      have hnat : (50002835397510404213 : ℕ)^1024*10000000000000000^4735 ≤ 10000122634953841^4735*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002835397510404213 50000000000000000000 10000122634953841 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000122634953841/10000000000000000 : ℝ)) (X := (50002835397510404213/50000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026009690246157743/100000000000000000000 : ℝ) ≤ (400022497325109/400000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (100026009690246157743/100000000000000000000 : ℝ)^1024 ≤ (400022497325109/400000000000000 : ℝ)^4735 := by
      have hnat : (100026009690246157743 : ℕ)^1024*400000000000000^4735 ≤ 400022497325109^4735*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026009690246157743 100000000000000000000 400022497325109 400000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400022497325109/400000000000000 : ℝ)) (X := (100026009690246157743/100000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002317429273575353/5000000000000000000 : ℝ) ≤ (10001002231301609/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (5002317429273575353/5000000000000000000 : ℝ)^1024 ≤ (10001002231301609/10000000000000000 : ℝ)^4735 := by
      have hnat : (5002317429273575353 : ℕ)^1024*10000000000000000^4735 ≤ 10001002231301609^4735*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002317429273575353 5000000000000000000 10001002231301609 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001002231301609/10000000000000000 : ℝ)) (X := (5002317429273575353/5000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2835397510404213/100000000000000000000 : ℝ) ≤ ((59741594617392238223/59750000000000000000 : ℝ)+2*(109949543471/149375000000000 : ℝ)*(10389/100000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (59741594617392238223/59750000000000000000 : ℝ)+2*(109949543471/149375000000000 : ℝ)*(10389/100000 : ℝ)=(10000122634953841/10000000000000000 : ℝ) by norm_num, show 1+2*(2835397510404213/100000000000000000000 : ℝ)=(50002835397510404213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2317429273575353/10000000000000000000 : ℝ)+(2835397510404213/100000000000000000000 : ℝ) ≤ ((59741594617392238223/59750000000000000000 : ℝ)+(109949543471/149375000000000 : ℝ)*((4091/25000 : ℝ)+(10389/100000 : ℝ)))^(4735/1024 : ℝ) := by
    rw [show (59741594617392238223/59750000000000000000 : ℝ)+(109949543471/149375000000000 : ℝ)*((4091/25000 : ℝ)+(10389/100000 : ℝ))=(400022497325109/400000000000000 : ℝ) by norm_num, show 1+(2317429273575353/10000000000000000000 : ℝ)+(2835397510404213/100000000000000000000 : ℝ)=(100026009690246157743/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2317429273575353/10000000000000000000 : ℝ) ≤ ((59741594617392238223/59750000000000000000 : ℝ)+2*(109949543471/149375000000000 : ℝ)*(4091/25000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (59741594617392238223/59750000000000000000 : ℝ)+2*(109949543471/149375000000000 : ℝ)*(4091/25000 : ℝ)=(10001002231301609/10000000000000000 : ℝ) by norm_num, show 1+2*(2317429273575353/10000000000000000000 : ℝ)=(5002317429273575353/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59741594617392238223/59750000000000000000 : ℝ)*(X 1 0+X 2 0)+(109949543471/149375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (59741594617392238223/59750000000000000000 : ℝ)) (alpha := (109949543471/149375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59741594617392238223/59750000000000000000 : ℝ)*(X 0 1+X 2 1)+(109949543471/149375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (59741594617392238223/59750000000000000000 : ℝ)) (alpha := (109949543471/149375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59741594617392238223/59750000000000000000 : ℝ)*(X 0 2+X 1 2)+(109949543471/149375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (59741594617392238223/59750000000000000000 : ℝ)) (alpha := (109949543471/149375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85847279/500000000 : ℝ)*X 0 0+(546099427/1000000000 : ℝ)*X 0 1+(647537771/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677134903/5000000000 : ℝ)*X 1 0+(-1861716189/10000000000 : ℝ)*X 1 1+(103606043/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354269723/10000000000 : ℝ)*X 2 0+(5180302287/10000000000 : ℝ)*X 2 1+(-1861716119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4216685861/10000000000 : ℝ)*X 0 0+(3884878433/10000000000 : ℝ)*X 0 1+(285630987/625000000 : ℝ)*X 0 2+(4216685861/10000000000 : ℝ)*X 1 0+(3884878433/10000000000 : ℝ)*X 1 1+(285630987/625000000 : ℝ)*X 1 2+(4216685861/10000000000 : ℝ)*X 2 0+(3884878433/10000000000 : ℝ)*X 2 1+(285630987/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-34340329/200000000 : ℝ)*X 0 0+(2591191973/5000000000 : ℝ)*X 0 1+(5458890809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055958677/2000000000 : ℝ)*X 1 0+(-1583127137/10000000000 : ℝ)*X 1 1+(109177827/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279793827/10000000000 : ℝ)*X 2 0+(5458890721/10000000000 : ℝ)*X 2 1+(-316625481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216859239/10000000000 : ℝ)*X 0 0+(4565014409/10000000000 : ℝ)*X 0 1+(1945006709/5000000000 : ℝ)*X 0 2+(4216859239/10000000000 : ℝ)*X 1 0+(4565014409/10000000000 : ℝ)*X 1 1+(1945006709/5000000000 : ℝ)*X 1 2+(4216859239/10000000000 : ℝ)*X 2 0+(4565014409/10000000000 : ℝ)*X 2 1+(1945006709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1108539694795811018005736643/149375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170565873/12500000000000 : ℝ)*(base19) + (252235159/20000000000000 : ℝ)*(base23) + (402609/1562500000000 : ℝ)*(lower2) + (84269783/50000000000000 : ℝ)*(upper3) + (88676191/50000000000000 : ℝ)*(upper5) + (251103099876153/10000000000000 : ℝ)*(major0) + (251103099876153/10000000000000 : ℝ)*(major1) + (251103099876153/10000000000000 : ℝ)*(major2) + (890659806352149/25000000000000 : ℝ)*(sp0) + (1781327593902959/50000000000000 : ℝ)*(sp1) + (1781327645578553/50000000000000 : ℝ)*(sp2) + (364849508527451/25000000000000 : ℝ)*(sp3) + (3465384861/20000000000000 : ℝ)*(sp4) + (447731717/6250000000000 : ℝ)*(sp7) + (364851299454319/25000000000000 : ℝ)*(f.failure) + (1781328276166451/50000000000000 : ℝ)*(f.sum) + (9090317523777/2987500000000000000000000000 : ℝ)*base65 + (2772256269672996119/597500000000000000000000000000000 : ℝ)*base67 + (2829688383740496119/597500000000000000000000000000000 : ℝ)*base69 + (339495845002003881/597500000000000000000000000000000 : ℝ)*base72 + (4116062637727/2987500000000000000000000000 : ℝ)*base73 + (768149174607996119/597500000000000000000000000000000 : ℝ)*base75 + (1956941791322996119/597500000000000000000000000000000 : ℝ)*base77 + (302102258902996119/597500000000000000000000000000000 : ℝ)*base79 + (5586516793877/2987500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (15797801/2500000000000000000000 : ℝ)*base90 + (15797801/2500000000000000000000 : ℝ)*base92 + (15797801/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85189362375141081323043/29875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211330859/100000000000000 : ℝ)*(base19) + (60052457/10000000000000 : ℝ)*(base23) + (57027753/25000000000000 : ℝ)*(lower1) + (7585767/25000000000000 : ℝ)*(upper3) + (6812787/12500000000000 : ℝ)*(lower4) + (637251909299893/25000000000000 : ℝ)*(major0) + (637251909299893/25000000000000 : ℝ)*(major1) + (637251909299893/25000000000000 : ℝ)*(major2) + (1190579819/100000000000000 : ℝ)*(sp1) + (97289447/25000000000000 : ℝ)*(sp3) + (904134512574143/25000000000000 : ℝ)*(sp4) + (1808268324192947/50000000000000 : ℝ)*(sp5) + (1808268724886001/50000000000000 : ℝ)*(sp6) + (740738369946943/50000000000000 : ℝ)*(sp7) + (740738564525837/50000000000000 : ℝ)*(f.failure) + (904134512574143/25000000000000 : ℝ)*(f.sum) + (22840159535199/14937500000000000000000000000 : ℝ)*base65 + (818584644458110139/1493750000000000000000000000000000 : ℝ)*base67 + (3028978517904389861/1493750000000000000000000000000000 : ℝ)*base70 + (6954415098066889861/1493750000000000000000000000000000 : ℝ)*base72 + (73342911396273/29875000000000000000000000000 : ℝ)*base73 + (382864485358110139/1493750000000000000000000000000000 : ℝ)*base75 + (19119328902129389861/1493750000000000000000000000000000 : ℝ)*base78 + (15738517651520610139/1493750000000000000000000000000000 : ℝ)*base79 + (15112440905949/14937500000000000000000000000 : ℝ)*base81 + (19492923/5000000000000000000000 : ℝ)*base90 + (19492923/5000000000000000000000 : ℝ)*base92 + (19492923/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1605_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (327/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1605_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1605_s5_0 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-858479067/5000000000 : ℝ)*x 0 + (682616991/1250000000 : ℝ)*x 1 + (647544013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858479067/5000000000 : ℝ)^4739 ≤ (1056402466007/10000000000000 : ℝ)^3715 := by
    have hnat : (858479067 : ℕ)^4739*10000000000000^3715 ≤ 1056402466007^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858479067 5000000000 1056402466007 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682616991/1250000000 : ℝ)^4739 ≤ (369775003781/800000000000 : ℝ)^3715 := by
    have hnat : (682616991 : ℕ)^4739*800000000000^3715 ≤ 369775003781^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682616991 1250000000 369775003781 800000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647544013/1250000000 : ℝ)^4739 ≤ (43214099846541/100000000000000 : ℝ)^3715 := by
    have hnat : (647544013 : ℕ)^4739*100000000000000^3715 ≤ 43214099846541^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647544013 1250000000 43214099846541 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-858479067/5000000000 : ℝ), (682616991/1250000000 : ℝ), (647544013/1250000000 : ℝ)] ![(1056402466007/10000000000000 : ℝ), (369775003781/800000000000 : ℝ), (43214099846541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-858479067/5000000000 : ℝ)|^4739 ≤ (1056402466007/10000000000000 : ℝ)^3715
        have hw : |(-858479067/5000000000 : ℝ)|=(858479067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682616991/1250000000 : ℝ)|^4739 ≤ (369775003781/800000000000 : ℝ)^3715
        have hw : |(682616991/1250000000 : ℝ)|=(682616991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647544013/1250000000 : ℝ)|^4739 ≤ (43214099846541/100000000000000 : ℝ)^3715
        have hw : |(647544013/1250000000 : ℝ)|=(647544013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s5_1 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669281713/1250000000 : ℝ)*x 0 + (-74466863/400000000 : ℝ)*x 1 + (323772003/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669281713/1250000000 : ℝ)^4739 ≤ (4507312952051/10000000000000 : ℝ)^3715 := by
    have hnat : (669281713 : ℕ)^4739*10000000000000^3715 ≤ 4507312952051^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669281713 1250000000 4507312952051 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74466863/400000000 : ℝ)^4739 ≤ (11712771215289/100000000000000 : ℝ)^3715 := by
    have hnat : (74466863 : ℕ)^4739*100000000000000^3715 ≤ 11712771215289^3715*400000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74466863 400000000 11712771215289 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323772003/625000000 : ℝ)^4739 ≤ (43214099250629/100000000000000 : ℝ)^3715 := by
    have hnat : (323772003 : ℕ)^4739*100000000000000^3715 ≤ 43214099250629^3715*625000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323772003 625000000 43214099250629 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669281713/1250000000 : ℝ), (-74466863/400000000 : ℝ), (323772003/625000000 : ℝ)] ![(4507312952051/10000000000000 : ℝ), (11712771215289/100000000000000 : ℝ), (43214099250629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669281713/1250000000 : ℝ)|^4739 ≤ (4507312952051/10000000000000 : ℝ)^3715
        have hw : |(669281713/1250000000 : ℝ)|=(669281713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-74466863/400000000 : ℝ)|^4739 ≤ (11712771215289/100000000000000 : ℝ)^3715
        have hw : |(-74466863/400000000 : ℝ)|=(74466863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323772003/625000000 : ℝ)|^4739 ≤ (43214099250629/100000000000000 : ℝ)^3715
        have hw : |(323772003/625000000 : ℝ)|=(323772003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s5_2 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677126961/5000000000 : ℝ)*x 0 + (5180352131/10000000000 : ℝ)*x 1 + (-1861671173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677126961/5000000000 : ℝ)^4739 ≤ (563414148269/1250000000000 : ℝ)^3715 := by
    have hnat : (2677126961 : ℕ)^4739*1250000000000^3715 ≤ 563414148269^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677126961 5000000000 563414148269 1250000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180352131/10000000000 : ℝ)^4739 ≤ (1350440629183/3125000000000 : ℝ)^3715 := by
    have hnat : (5180352131 : ℕ)^4739*3125000000000^3715 ≤ 1350440629183^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180352131 10000000000 1350440629183 3125000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1861671173/10000000000 : ℝ)^4739 ≤ (5856383994473/50000000000000 : ℝ)^3715 := by
    have hnat : (1861671173 : ℕ)^4739*50000000000000^3715 ≤ 5856383994473^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861671173 10000000000 5856383994473 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677126961/5000000000 : ℝ), (5180352131/10000000000 : ℝ), (-1861671173/10000000000 : ℝ)] ![(563414148269/1250000000000 : ℝ), (1350440629183/3125000000000 : ℝ), (5856383994473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677126961/5000000000 : ℝ)|^4739 ≤ (563414148269/1250000000000 : ℝ)^3715
        have hw : |(2677126961/5000000000 : ℝ)|=(2677126961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180352131/10000000000 : ℝ)|^4739 ≤ (1350440629183/3125000000000 : ℝ)^3715
        have hw : |(5180352131/10000000000 : ℝ)|=(5180352131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1861671173/10000000000 : ℝ)|^4739 ≤ (5856383994473/50000000000000 : ℝ)^3715
        have hw : |(-1861671173/10000000000 : ℝ)|=(1861671173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s5_3 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (843338507/2000000000 : ℝ)*x 0 + (1942505023/5000000000 : ℝ)*x 1 + (1142490853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843338507/2000000000 : ℝ)^4739 ≤ (33235289166453/100000000000000 : ℝ)^3715 := by
    have hnat : (843338507 : ℕ)^4739*100000000000000^3715 ≤ 33235289166453^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843338507 2000000000 33235289166453 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942505023/5000000000 : ℝ)^4739 ≤ (29937290024039/100000000000000 : ℝ)^3715 := by
    have hnat : (1942505023 : ℕ)^4739*100000000000000^3715 ≤ 29937290024039^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942505023 5000000000 29937290024039 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142490853/2500000000 : ℝ)^4739 ≤ (18413710392703/50000000000000 : ℝ)^3715 := by
    have hnat : (1142490853 : ℕ)^4739*50000000000000^3715 ≤ 18413710392703^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142490853 2500000000 18413710392703 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843338507/2000000000 : ℝ), (1942505023/5000000000 : ℝ), (1142490853/2500000000 : ℝ)] ![(33235289166453/100000000000000 : ℝ), (29937290024039/100000000000000 : ℝ), (18413710392703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843338507/2000000000 : ℝ)|^4739 ≤ (33235289166453/100000000000000 : ℝ)^3715
        have hw : |(843338507/2000000000 : ℝ)|=(843338507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1942505023/5000000000 : ℝ)|^4739 ≤ (29937290024039/100000000000000 : ℝ)^3715
        have hw : |(1942505023/5000000000 : ℝ)|=(1942505023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1142490853/2500000000 : ℝ)|^4739 ≤ (18413710392703/50000000000000 : ℝ)^3715
        have hw : |(1142490853/2500000000 : ℝ)|=(1142490853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s5_4 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1717028939/10000000000 : ℝ)*x 0 + (5182431943/10000000000 : ℝ)*x 1 + (2729417207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1717028939/10000000000 : ℝ)^4739 ≤ (2112916078051/20000000000000 : ℝ)^3715 := by
    have hnat : (1717028939 : ℕ)^4739*20000000000000^3715 ≤ 2112916078051^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717028939 10000000000 2112916078051 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182431943/10000000000 : ℝ)^4739 ≤ (43236233230987/100000000000000 : ℝ)^3715 := by
    have hnat : (5182431943 : ℕ)^4739*100000000000000^3715 ≤ 43236233230987^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182431943 10000000000 43236233230987 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729417207/5000000000 : ℝ)^4739 ≤ (46199186354091/100000000000000 : ℝ)^3715 := by
    have hnat : (2729417207 : ℕ)^4739*100000000000000^3715 ≤ 46199186354091^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729417207 5000000000 46199186354091 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1717028939/10000000000 : ℝ), (5182431943/10000000000 : ℝ), (2729417207/5000000000 : ℝ)] ![(2112916078051/20000000000000 : ℝ), (43236233230987/100000000000000 : ℝ), (46199186354091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1717028939/10000000000 : ℝ)|^4739 ≤ (2112916078051/20000000000000 : ℝ)^3715
        have hw : |(-1717028939/10000000000 : ℝ)|=(1717028939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182431943/10000000000 : ℝ)|^4739 ≤ (43236233230987/100000000000000 : ℝ)^3715
        have hw : |(5182431943/10000000000 : ℝ)|=(5182431943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729417207/5000000000 : ℝ)|^4739 ≤ (46199186354091/100000000000000 : ℝ)^3715
        have hw : |(2729417207/5000000000 : ℝ)|=(2729417207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s5_5 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279806559/10000000000 : ℝ)*x 0 + (-395797211/2500000000 : ℝ)*x 1 + (5458834427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279806559/10000000000 : ℝ)^4739 ≤ (44275210425311/100000000000000 : ℝ)^3715 := by
    have hnat : (5279806559 : ℕ)^4739*100000000000000^3715 ≤ 44275210425311^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279806559 10000000000 44275210425311 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395797211/2500000000 : ℝ)^4739 ≤ (4762801532453/50000000000000 : ℝ)^3715 := by
    have hnat : (395797211 : ℕ)^4739*50000000000000^3715 ≤ 4762801532453^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395797211 2500000000 4762801532453 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458834427/10000000000 : ℝ)^4739 ≤ (46199186494439/100000000000000 : ℝ)^3715 := by
    have hnat : (5458834427 : ℕ)^4739*100000000000000^3715 ≤ 46199186494439^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458834427 10000000000 46199186494439 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279806559/10000000000 : ℝ), (-395797211/2500000000 : ℝ), (5458834427/10000000000 : ℝ)] ![(44275210425311/100000000000000 : ℝ), (4762801532453/50000000000000 : ℝ), (46199186494439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279806559/10000000000 : ℝ)|^4739 ≤ (44275210425311/100000000000000 : ℝ)^3715
        have hw : |(5279806559/10000000000 : ℝ)|=(5279806559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395797211/2500000000 : ℝ)|^4739 ≤ (4762801532453/50000000000000 : ℝ)^3715
        have hw : |(-395797211/2500000000 : ℝ)|=(395797211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458834427/10000000000 : ℝ)|^4739 ≤ (46199186494439/100000000000000 : ℝ)^3715
        have hw : |(5458834427/10000000000 : ℝ)|=(5458834427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s5_6 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639903283/5000000000 : ℝ)*x 0 + (1364708607/2500000000 : ℝ)*x 1 + (-1583188833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639903283/5000000000 : ℝ)^4739 ≤ (1383600328131/3125000000000 : ℝ)^3715 := by
    have hnat : (2639903283 : ℕ)^4739*3125000000000^3715 ≤ 1383600328131^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639903283 5000000000 1383600328131 3125000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364708607/2500000000 : ℝ)^4739 ≤ (9239837301047/20000000000000 : ℝ)^3715 := by
    have hnat : (1364708607 : ℕ)^4739*20000000000000^3715 ≤ 9239837301047^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364708607 2500000000 9239837301047 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583188833/10000000000 : ℝ)^4739 ≤ (9525602980479/100000000000000 : ℝ)^3715 := by
    have hnat : (1583188833 : ℕ)^4739*100000000000000^3715 ≤ 9525602980479^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583188833 10000000000 9525602980479 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639903283/5000000000 : ℝ), (1364708607/2500000000 : ℝ), (-1583188833/10000000000 : ℝ)] ![(1383600328131/3125000000000 : ℝ), (9239837301047/20000000000000 : ℝ), (9525602980479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639903283/5000000000 : ℝ)|^4739 ≤ (1383600328131/3125000000000 : ℝ)^3715
        have hw : |(2639903283/5000000000 : ℝ)|=(2639903283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364708607/2500000000 : ℝ)|^4739 ≤ (9239837301047/20000000000000 : ℝ)^3715
        have hw : |(1364708607/2500000000 : ℝ)|=(1364708607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1583188833/10000000000 : ℝ)|^4739 ≤ (9525602980479/100000000000000 : ℝ)^3715
        have hw : |(-1583188833/10000000000 : ℝ)|=(1583188833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s5_7 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4216866703/10000000000 : ℝ)*x 0 + (182595431/400000000 : ℝ)*x 1 + (3890140219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216866703/10000000000 : ℝ)^4739 ≤ (3323704032817/10000000000000 : ℝ)^3715 := by
    have hnat : (4216866703 : ℕ)^4739*10000000000000^3715 ≤ 3323704032817^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216866703 10000000000 3323704032817 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182595431/400000000 : ℝ)^4739 ≤ (36775231470589/100000000000000 : ℝ)^3715 := by
    have hnat : (182595431 : ℕ)^4739*100000000000000^3715 ≤ 36775231470589^3715*400000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182595431 400000000 36775231470589 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3890140219/10000000000 : ℝ)^4739 ≤ (14993864092619/50000000000000 : ℝ)^3715 := by
    have hnat : (3890140219 : ℕ)^4739*50000000000000^3715 ≤ 14993864092619^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3890140219 10000000000 14993864092619 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216866703/10000000000 : ℝ), (182595431/400000000 : ℝ), (3890140219/10000000000 : ℝ)] ![(3323704032817/10000000000000 : ℝ), (36775231470589/100000000000000 : ℝ), (14993864092619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216866703/10000000000 : ℝ)|^4739 ≤ (3323704032817/10000000000000 : ℝ)^3715
        have hw : |(4216866703/10000000000 : ℝ)|=(4216866703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(182595431/400000000 : ℝ)|^4739 ≤ (36775231470589/100000000000000 : ℝ)^3715
        have hw : |(182595431/400000000 : ℝ)|=(182595431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3890140219/10000000000 : ℝ)|^4739 ≤ (14993864092619/50000000000000 : ℝ)^3715
        have hw : |(3890140219/10000000000 : ℝ)|=(3890140219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1605_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5201/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16349/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (327/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (327/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (327/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (327/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (327/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (327/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10401/100000 : ℝ) ^ (4735/1024 : ℝ) ≤ (2850573269504183/100000000000000000000 : ℝ) := by
    have hpowers : (10401/100000 : ℝ)^4735 ≤ (2850573269504183/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10401 : ℕ)^4735*100000000000000000000^1024 ≤ 2850573269504183^1024*100000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10401 100000 2850573269504183 100000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10401/100000 : ℝ)) (X := (2850573269504183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (327/2000 : ℝ) ^ (4735/1024 : ℝ) ≤ (11541378381562717/50000000000000000000 : ℝ) := by
    have hpowers : (327/2000 : ℝ)^4735 ≤ (11541378381562717/50000000000000000000 : ℝ)^1024 := by
      have hnat : (327 : ℕ)^4735*50000000000000000000^1024 ≤ 11541378381562717^1024*2000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        327 2000 11541378381562717 50000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (327/2000 : ℝ)) (X := (11541378381562717/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002850573269504183/50000000000000000000 : ℝ) ≤ (10000123291312229/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (50002850573269504183/50000000000000000000 : ℝ)^1024 ≤ (10000123291312229/10000000000000000 : ℝ)^4735 := by
      have hnat : (50002850573269504183 : ℕ)^1024*10000000000000000^4735 ≤ 10000123291312229^4735*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002850573269504183 50000000000000000000 10000123291312229 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000123291312229/10000000000000000 : ℝ)) (X := (50002850573269504183/50000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025933330032629617/100000000000000000000 : ℝ) ≤ (10000560782083453/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (100025933330032629617/100000000000000000000 : ℝ)^1024 ≤ (10000560782083453/10000000000000000 : ℝ)^4735 := by
      have hnat : (100025933330032629617 : ℕ)^1024*10000000000000000^4735 ≤ 10000560782083453^4735*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025933330032629617 100000000000000000000 10000560782083453 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000560782083453/10000000000000000 : ℝ)) (X := (100025933330032629617/100000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011541378381562717/25000000000000000000 : ℝ) ≤ (10000998272854677/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (25011541378381562717/25000000000000000000 : ℝ)^1024 ≤ (10000998272854677/10000000000000000 : ℝ)^4735 := by
      have hnat : (25011541378381562717 : ℕ)^1024*10000000000000000^4735 ≤ 10000998272854677^4735*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011541378381562717 25000000000000000000 10000998272854677 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000998272854677/10000000000000000 : ℝ)) (X := (25011541378381562717/25000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2850573269504183/100000000000000000000 : ℝ) ≤ ((19827210925664482891/19830000000000000000 : ℝ)+2*(54686346403/74362500000000 : ℝ)*(10401/100000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (19827210925664482891/19830000000000000000 : ℝ)+2*(54686346403/74362500000000 : ℝ)*(10401/100000 : ℝ)=(10000123291312229/10000000000000000 : ℝ) by norm_num, show 1+2*(2850573269504183/100000000000000000000 : ℝ)=(50002850573269504183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11541378381562717/50000000000000000000 : ℝ)+(2850573269504183/100000000000000000000 : ℝ) ≤ ((19827210925664482891/19830000000000000000 : ℝ)+(54686346403/74362500000000 : ℝ)*((327/2000 : ℝ)+(10401/100000 : ℝ)))^(4735/1024 : ℝ) := by
    rw [show (19827210925664482891/19830000000000000000 : ℝ)+(54686346403/74362500000000 : ℝ)*((327/2000 : ℝ)+(10401/100000 : ℝ))=(10000560782083453/10000000000000000 : ℝ) by norm_num, show 1+(11541378381562717/50000000000000000000 : ℝ)+(2850573269504183/100000000000000000000 : ℝ)=(100025933330032629617/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11541378381562717/50000000000000000000 : ℝ) ≤ ((19827210925664482891/19830000000000000000 : ℝ)+2*(54686346403/74362500000000 : ℝ)*(327/2000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (19827210925664482891/19830000000000000000 : ℝ)+2*(54686346403/74362500000000 : ℝ)*(327/2000 : ℝ)=(10000998272854677/10000000000000000 : ℝ) by norm_num, show 1+2*(11541378381562717/50000000000000000000 : ℝ)=(25011541378381562717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19827210925664482891/19830000000000000000 : ℝ)*(X 1 0+X 2 0)+(54686346403/74362500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10401/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (19827210925664482891/19830000000000000000 : ℝ)) (alpha := (54686346403/74362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19827210925664482891/19830000000000000000 : ℝ)*(X 0 1+X 2 1)+(54686346403/74362500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10401/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (19827210925664482891/19830000000000000000 : ℝ)) (alpha := (54686346403/74362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19827210925664482891/19830000000000000000 : ℝ)*(X 0 2+X 1 2)+(54686346403/74362500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (10401/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (19827210925664482891/19830000000000000000 : ℝ)) (alpha := (54686346403/74362500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-858479067/5000000000 : ℝ)*X 0 0+(682616991/1250000000 : ℝ)*X 0 1+(647544013/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669281713/1250000000 : ℝ)*X 1 0+(-74466863/400000000 : ℝ)*X 1 1+(323772003/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677126961/5000000000 : ℝ)*X 2 0+(5180352131/10000000000 : ℝ)*X 2 1+(-1861671173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((843338507/2000000000 : ℝ)*X 0 0+(1942505023/5000000000 : ℝ)*X 0 1+(1142490853/2500000000 : ℝ)*X 0 2+(843338507/2000000000 : ℝ)*X 1 0+(1942505023/5000000000 : ℝ)*X 1 1+(1142490853/2500000000 : ℝ)*X 1 2+(843338507/2000000000 : ℝ)*X 2 0+(1942505023/5000000000 : ℝ)*X 2 1+(1142490853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1717028939/10000000000 : ℝ)*X 0 0+(5182431943/10000000000 : ℝ)*X 0 1+(2729417207/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279806559/10000000000 : ℝ)*X 1 0+(-395797211/2500000000 : ℝ)*X 1 1+(5458834427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639903283/5000000000 : ℝ)*X 2 0+(1364708607/2500000000 : ℝ)*X 2 1+(-1583188833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216866703/10000000000 : ℝ)*X 0 0+(182595431/400000000 : ℝ)*X 0 1+(3890140219/10000000000 : ℝ)*X 0 2+(4216866703/10000000000 : ℝ)*X 1 0+(182595431/400000000 : ℝ)*X 1 1+(3890140219/10000000000 : ℝ)*X 1 2+(4216866703/10000000000 : ℝ)*X 2 0+(182595431/400000000 : ℝ)*X 2 1+(3890140219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (894875122144978840854405911/99150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (250666057/20000000000000 : ℝ)*(base19) + (1135718411/100000000000000 : ℝ)*(base23) + (25698193/25000000000000 : ℝ)*(upper3) + (35167029/25000000000000 : ℝ)*(upper4) + (121494519/50000000000000 : ℝ)*(upper5) + (251199602332531/10000000000000 : ℝ)*(major0) + (251199602332531/10000000000000 : ℝ)*(major1) + (251199602332531/10000000000000 : ℝ)*(major2) + (13921907791819/390625000000 : ℝ)*(sp0) + (3564024424690713/100000000000000 : ℝ)*(sp1) + (1782012271151293/50000000000000 : ℝ)*(sp2) + (364989957005587/25000000000000 : ℝ)*(sp3) + (8641657667/50000000000000 : ℝ)*(sp4) + (311987917/5000000000000 : ℝ)*(sp7) + (91247879236293/6250000000000 : ℝ)*(f.failure) + (1782012839010499/50000000000000 : ℝ)*(f.sum) + (7858383714307/2974500000000000000000000000 : ℝ)*base66 + (7037528699697281363/594900000000000000000000000000000 : ℝ)*base67 + (5718577393377881363/594900000000000000000000000000000 : ℝ)*base69 + (3878702212596281363/594900000000000000000000000000000 : ℝ)*base71 + (3431071043071/5949000000000000000000000000 : ℝ)*base73 + (2958295593527081363/594900000000000000000000000000000 : ℝ)*base75 + (5742767024430281363/594900000000000000000000000000000 : ℝ)*base77 + (8437982425618481363/594900000000000000000000000000000 : ℝ)*base79 + (7552756397377/2974500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4397347/625000000000000000000 : ℝ)*base90 + (4397347/625000000000000000000 : ℝ)*base92 + (4397347/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2518841827084625380926484189/495750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777540469/100000000000000 : ℝ)*(base19) + (26593399/3125000000000 : ℝ)*(base23) + (49866259/20000000000000 : ℝ)*(lower1) + (54232993/50000000000000 : ℝ)*(upper3) + (29630353/100000000000000 : ℝ)*(lower4) + (104571857/100000000000000 : ℝ)*(upper5) + (1274984929098707/50000000000000 : ℝ)*(major0) + (1274984929098707/50000000000000 : ℝ)*(major1) + (1274984929098707/50000000000000 : ℝ)*(major2) + (444367571/50000000000000 : ℝ)*(sp2) + (904475794360791/25000000000000 : ℝ)*(sp4) + (1808951199951347/50000000000000 : ℝ)*(sp5) + (1808950718859627/50000000000000 : ℝ)*(sp6) + (1482036369589283/100000000000000 : ℝ)*(sp7) + (1482036369589283/100000000000000 : ℝ)*(f.failure) + (904475794360791/25000000000000 : ℝ)*(f.sum) + (152427092167751/29745000000000000000000000000 : ℝ)*base65 + (32043141224205465811/2974500000000000000000000000000000 : ℝ)*base67 + (29863586175446534189/2974500000000000000000000000000000 : ℝ)*base70 + (60862842931614465811/2974500000000000000000000000000000 : ℝ)*base71 + (31062059659931/29745000000000000000000000000 : ℝ)*base73 + (162631180009824465811/2974500000000000000000000000000000 : ℝ)*base75 + (5360172036464534189/2974500000000000000000000000000000 : ℝ)*base78 + (7927749343086465811/2974500000000000000000000000000000 : ℝ)*base79 + (187906270643869/29745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10430443/10000000000000000000000 : ℝ)*base89 + (10430443/10000000000000000000000 : ℝ)*base91 + (10430443/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1605_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5201/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1605_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1605_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3303/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5201/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1605_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1605_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1605_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3303/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5201/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1605_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
