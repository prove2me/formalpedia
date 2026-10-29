-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1572_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:53.185895+00:00
-- url     : https://prove2.me/submissions/953b7c4c-7a96-455e-8d49-be7e9617c250

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
theorem support_rectangle_w1572_s0_0 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-162400459/1000000000 : ℝ)*x 0 + (146702551/250000000 : ℝ)*x 1 + (4880153153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162400459/1000000000 : ℝ)^4641 ≤ (9707302095669/100000000000000 : ℝ)^3617 := by
    have hnat : (162400459 : ℕ)^4641*100000000000000^3617 ≤ 9707302095669^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162400459 1000000000 9707302095669 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146702551/250000000 : ℝ)^4641 ≤ (50461202611437/100000000000000 : ℝ)^3617 := by
    have hnat : (146702551 : ℕ)^4641*100000000000000^3617 ≤ 50461202611437^3617*250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146702551 250000000 50461202611437 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880153153/10000000000 : ℝ)^4641 ≤ (19915747637899/50000000000000 : ℝ)^3617 := by
    have hnat : (4880153153 : ℕ)^4641*50000000000000^3617 ≤ 19915747637899^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880153153 10000000000 19915747637899 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-162400459/1000000000 : ℝ), (146702551/250000000 : ℝ), (4880153153/10000000000 : ℝ)] ![(9707302095669/100000000000000 : ℝ), (50461202611437/100000000000000 : ℝ), (19915747637899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-162400459/1000000000 : ℝ)|^4641 ≤ (9707302095669/100000000000000 : ℝ)^3617
        have hw : |(-162400459/1000000000 : ℝ)|=(162400459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146702551/250000000 : ℝ)|^4641 ≤ (50461202611437/100000000000000 : ℝ)^3617
        have hw : |(146702551/250000000 : ℝ)|=(146702551/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880153153/10000000000 : ℝ)|^4641 ≤ (19915747637899/50000000000000 : ℝ)^3617
        have hw : |(4880153153/10000000000 : ℝ)|=(4880153153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s0_1 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2732525977/5000000000 : ℝ)*x 0 + (-543411481/2500000000 : ℝ)*x 1 + (4880153153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2732525977/5000000000 : ℝ)^4641 ≤ (23029009749631/50000000000000 : ℝ)^3617 := by
    have hnat : (2732525977 : ℕ)^4641*50000000000000^3617 ≤ 23029009749631^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732525977 5000000000 23029009749631 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543411481/2500000000 : ℝ)^4641 ≤ (2822097042999/20000000000000 : ℝ)^3617 := by
    have hnat : (543411481 : ℕ)^4641*20000000000000^3617 ≤ 2822097042999^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543411481 2500000000 2822097042999 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880153153/10000000000 : ℝ)^4641 ≤ (19915747637899/50000000000000 : ℝ)^3617 := by
    have hnat : (4880153153 : ℕ)^4641*50000000000000^3617 ≤ 19915747637899^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880153153 10000000000 19915747637899 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2732525977/5000000000 : ℝ), (-543411481/2500000000 : ℝ), (4880153153/10000000000 : ℝ)] ![(23029009749631/50000000000000 : ℝ), (2822097042999/20000000000000 : ℝ), (19915747637899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2732525977/5000000000 : ℝ)|^4641 ≤ (23029009749631/50000000000000 : ℝ)^3617
        have hw : |(2732525977/5000000000 : ℝ)|=(2732525977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543411481/2500000000 : ℝ)|^4641 ≤ (2822097042999/20000000000000 : ℝ)^3617
        have hw : |(-543411481/2500000000 : ℝ)|=(543411481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880153153/10000000000 : ℝ)|^4641 ≤ (19915747637899/50000000000000 : ℝ)^3617
        have hw : |(4880153153/10000000000 : ℝ)|=(4880153153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s0_2 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1366263003/2500000000 : ℝ)*x 0 + (4880153083/10000000000 : ℝ)*x 1 + (-2173645937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1366263003/2500000000 : ℝ)^4641 ≤ (5757252515807/12500000000000 : ℝ)^3617 := by
    have hnat : (1366263003 : ℕ)^4641*12500000000000^3617 ≤ 5757252515807^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366263003 2500000000 5757252515807 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4880153083/10000000000 : ℝ)^4641 ≤ (39831494542713/100000000000000 : ℝ)^3617 := by
    have hnat : (4880153083 : ℕ)^4641*100000000000000^3617 ≤ 39831494542713^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880153083 10000000000 39831494542713 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173645937/10000000000 : ℝ)^4641 ≤ (14110485323277/100000000000000 : ℝ)^3617 := by
    have hnat : (2173645937 : ℕ)^4641*100000000000000^3617 ≤ 14110485323277^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173645937 10000000000 14110485323277 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1366263003/2500000000 : ℝ), (4880153083/10000000000 : ℝ), (-2173645937/10000000000 : ℝ)] ![(5757252515807/12500000000000 : ℝ), (39831494542713/100000000000000 : ℝ), (14110485323277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1366263003/2500000000 : ℝ)|^4641 ≤ (5757252515807/12500000000000 : ℝ)^3617
        have hw : |(1366263003/2500000000 : ℝ)|=(1366263003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4880153083/10000000000 : ℝ)|^4641 ≤ (39831494542713/100000000000000 : ℝ)^3617
        have hw : |(4880153083/10000000000 : ℝ)|=(4880153083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173645937/10000000000 : ℝ)|^4641 ≤ (14110485323277/100000000000000 : ℝ)^3617
        have hw : |(-2173645937/10000000000 : ℝ)|=(2173645937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s0_3 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4129335043/10000000000 : ℝ)*x 0 + (3093273111/10000000000 : ℝ)*x 1 + (1357141371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4129335043/10000000000 : ℝ)^4641 ≤ (32146440020337/100000000000000 : ℝ)^3617 := by
    have hnat : (4129335043 : ℕ)^4641*100000000000000^3617 ≤ 32146440020337^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129335043 10000000000 32146440020337 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093273111/10000000000 : ℝ)^4641 ≤ (22189720474869/100000000000000 : ℝ)^3617 := by
    have hnat : (3093273111 : ℕ)^4641*100000000000000^3617 ≤ 22189720474869^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093273111 10000000000 22189720474869 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357141371/2500000000 : ℝ)^4641 ≤ (45663839497749/100000000000000 : ℝ)^3617 := by
    have hnat : (1357141371 : ℕ)^4641*100000000000000^3617 ≤ 45663839497749^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357141371 2500000000 45663839497749 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4129335043/10000000000 : ℝ), (3093273111/10000000000 : ℝ), (1357141371/2500000000 : ℝ)] ![(32146440020337/100000000000000 : ℝ), (22189720474869/100000000000000 : ℝ), (45663839497749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4129335043/10000000000 : ℝ)|^4641 ≤ (32146440020337/100000000000000 : ℝ)^3617
        have hw : |(4129335043/10000000000 : ℝ)|=(4129335043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093273111/10000000000 : ℝ)|^4641 ≤ (22189720474869/100000000000000 : ℝ)^3617
        have hw : |(3093273111/10000000000 : ℝ)|=(3093273111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357141371/2500000000 : ℝ)|^4641 ≤ (45663839497749/100000000000000 : ℝ)^3617
        have hw : |(1357141371/2500000000 : ℝ)|=(1357141371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s0_4 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1627044089/10000000000 : ℝ)*x 0 + (1226259931/2500000000 : ℝ)*x 1 + (2921167321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1627044089/10000000000 : ℝ)^4641 ≤ (9730620098449/100000000000000 : ℝ)^3617 := by
    have hnat : (1627044089 : ℕ)^4641*100000000000000^3617 ≤ 9730620098449^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627044089 10000000000 9730620098449 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1226259931/2500000000 : ℝ)^4641 ≤ (20046155654527/50000000000000 : ℝ)^3617 := by
    have hnat : (1226259931 : ℕ)^4641*50000000000000^3617 ≤ 20046155654527^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226259931 2500000000 20046155654527 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2921167321/5000000000 : ℝ)^4641 ≤ (12544267145607/25000000000000 : ℝ)^3617 := by
    have hnat : (2921167321 : ℕ)^4641*25000000000000^3617 ≤ 12544267145607^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2921167321 5000000000 12544267145607 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1627044089/10000000000 : ℝ), (1226259931/2500000000 : ℝ), (2921167321/5000000000 : ℝ)] ![(9730620098449/100000000000000 : ℝ), (20046155654527/50000000000000 : ℝ), (12544267145607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1627044089/10000000000 : ℝ)|^4641 ≤ (9730620098449/100000000000000 : ℝ)^3617
        have hw : |(-1627044089/10000000000 : ℝ)|=(1627044089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1226259931/2500000000 : ℝ)|^4641 ≤ (20046155654527/50000000000000 : ℝ)^3617
        have hw : |(1226259931/2500000000 : ℝ)|=(1226259931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2921167321/5000000000 : ℝ)|^4641 ≤ (12544267145607/25000000000000 : ℝ)^3617
        have hw : |(2921167321/5000000000 : ℝ)|=(2921167321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s0_5 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298742247/2500000000 : ℝ)*x 0 + (-1211464781/10000000000 : ℝ)*x 1 + (584233437/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298742247/2500000000 : ℝ)^4641 ≤ (67434536133/156250000000 : ℝ)^3617 := by
    have hnat : (1298742247 : ℕ)^4641*156250000000^3617 ≤ 67434536133^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298742247 2500000000 67434536133 156250000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1211464781/10000000000 : ℝ)^4641 ≤ (3332415640017/50000000000000 : ℝ)^3617 := by
    have hnat : (1211464781 : ℕ)^4641*50000000000000^3617 ≤ 3332415640017^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211464781 10000000000 3332415640017 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (584233437/1000000000 : ℝ)^4641 ≤ (25088532792493/50000000000000 : ℝ)^3617 := by
    have hnat : (584233437 : ℕ)^4641*50000000000000^3617 ≤ 25088532792493^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584233437 1000000000 25088532792493 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298742247/2500000000 : ℝ), (-1211464781/10000000000 : ℝ), (584233437/1000000000 : ℝ)] ![(67434536133/156250000000 : ℝ), (3332415640017/50000000000000 : ℝ), (25088532792493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298742247/2500000000 : ℝ)|^4641 ≤ (67434536133/156250000000 : ℝ)^3617
        have hw : |(1298742247/2500000000 : ℝ)|=(1298742247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1211464781/10000000000 : ℝ)|^4641 ≤ (3332415640017/50000000000000 : ℝ)^3617
        have hw : |(-1211464781/10000000000 : ℝ)|=(1211464781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(584233437/1000000000 : ℝ)|^4641 ≤ (25088532792493/50000000000000 : ℝ)^3617
        have hw : |(584233437/1000000000 : ℝ)|=(584233437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s0_6 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649371081/1250000000 : ℝ)*x 0 + (233693397/400000000 : ℝ)*x 1 + (-302866107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649371081/1250000000 : ℝ)^4641 ≤ (43158099500843/100000000000000 : ℝ)^3617 := by
    have hnat : (649371081 : ℕ)^4641*100000000000000^3617 ≤ 43158099500843^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649371081 1250000000 43158099500843 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233693397/400000000 : ℝ)^4641 ≤ (5017707170109/10000000000000 : ℝ)^3617 := by
    have hnat : (233693397 : ℕ)^4641*10000000000000^3617 ≤ 5017707170109^3617*400000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233693397 400000000 5017707170109 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302866107/2500000000 : ℝ)^4641 ≤ (6664828788217/100000000000000 : ℝ)^3617 := by
    have hnat : (302866107 : ℕ)^4641*100000000000000^3617 ≤ 6664828788217^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302866107 2500000000 6664828788217 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649371081/1250000000 : ℝ), (233693397/400000000 : ℝ), (-302866107/2500000000 : ℝ)] ![(43158099500843/100000000000000 : ℝ), (5017707170109/10000000000000 : ℝ), (6664828788217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649371081/1250000000 : ℝ)|^4641 ≤ (43158099500843/100000000000000 : ℝ)^3617
        have hw : |(649371081/1250000000 : ℝ)|=(649371081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(233693397/400000000 : ℝ)|^4641 ≤ (5017707170109/10000000000000 : ℝ)^3617
        have hw : |(233693397/400000000 : ℝ)|=(233693397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302866107/2500000000 : ℝ)|^4641 ≤ (6664828788217/100000000000000 : ℝ)^3617
        have hw : |(-302866107/2500000000 : ℝ)|=(302866107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s0_7 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034129637/2500000000 : ℝ)*x 0 + (5369738311/10000000000 : ℝ)*x 1 + (197136361/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034129637/2500000000 : ℝ)^4641 ≤ (32218212691407/100000000000000 : ℝ)^3617 := by
    have hnat : (1034129637 : ℕ)^4641*100000000000000^3617 ≤ 32218212691407^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034129637 2500000000 32218212691407 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5369738311/10000000000 : ℝ)^4641 ≤ (45029882290141/100000000000000 : ℝ)^3617 := by
    have hnat : (5369738311 : ℕ)^4641*100000000000000^3617 ≤ 45029882290141^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369738311 10000000000 45029882290141 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197136361/625000000 : ℝ)^4641 ≤ (5687976252271/25000000000000 : ℝ)^3617 := by
    have hnat : (197136361 : ℕ)^4641*25000000000000^3617 ≤ 5687976252271^3617*625000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197136361 625000000 5687976252271 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034129637/2500000000 : ℝ), (5369738311/10000000000 : ℝ), (197136361/625000000 : ℝ)] ![(32218212691407/100000000000000 : ℝ), (45029882290141/100000000000000 : ℝ), (5687976252271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034129637/2500000000 : ℝ)|^4641 ≤ (32218212691407/100000000000000 : ℝ)^3617
        have hw : |(1034129637/2500000000 : ℝ)|=(1034129637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5369738311/10000000000 : ℝ)|^4641 ≤ (45029882290141/100000000000000 : ℝ)^3617
        have hw : |(5369738311/10000000000 : ℝ)|=(5369738311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197136361/625000000 : ℝ)|^4641 ≤ (5687976252271/25000000000000 : ℝ)^3617
        have hw : |(197136361/625000000 : ℝ)|=(197136361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1572_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (223/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2473/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4639/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4639 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4639*1^1024 ≤ 0^1024*1^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4639/1024 : ℝ) ≤ (1574791090222121389/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4639 ≤ (1574791090222121389/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4639*100000000000000000000^1024 ≤ 1574791090222121389^1024*5^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1574791090222121389 100000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1574791090222121389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4639 := by
      have hnat : (1 : ℕ)^1024*1^4639 ≤ 1^4639*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101574791090222121389/100000000000000000000 : ℝ) ≤ (2508637545034859/2500000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (101574791090222121389/100000000000000000000 : ℝ)^1024 ≤ (2508637545034859/2500000000000000 : ℝ)^4639 := by
      have hnat : (101574791090222121389 : ℕ)^1024*2500000000000000^4639 ≤ 2508637545034859^4639*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101574791090222121389 100000000000000000000 2508637545034859 2500000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508637545034859/2500000000000000 : ℝ)) (X := (101574791090222121389/100000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51574791090222121389/50000000000000000000 : ℝ) ≤ (1258637545034859/1250000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (51574791090222121389/50000000000000000000 : ℝ)^1024 ≤ (1258637545034859/1250000000000000 : ℝ)^4639 := by
      have hnat : (51574791090222121389 : ℕ)^1024*1250000000000000^4639 ≤ 1258637545034859^4639*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51574791090222121389 50000000000000000000 1258637545034859 1250000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1258637545034859/1250000000000000 : ℝ)) (X := (51574791090222121389/50000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8637545034859/1000000000000000 : ℝ)*(0 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8637545034859/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1574791090222121389/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8637545034859/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4639/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8637545034859/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2508637545034859/2500000000000000 : ℝ) by norm_num, show 1+(1574791090222121389/100000000000000000000 : ℝ)+(0 : ℝ)=(101574791090222121389/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1574791090222121389/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8637545034859/1000000000000000 : ℝ)*(2/5 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8637545034859/1000000000000000 : ℝ)*(2/5 : ℝ)=(1258637545034859/1250000000000000 : ℝ) by norm_num, show 1+2*(1574791090222121389/100000000000000000000 : ℝ)=(51574791090222121389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8637545034859/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8637545034859/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8637545034859/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8637545034859/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8637545034859/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8637545034859/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-162400459/1000000000 : ℝ)*X 0 0+(146702551/250000000 : ℝ)*X 0 1+(4880153153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2732525977/5000000000 : ℝ)*X 1 0+(-543411481/2500000000 : ℝ)*X 1 1+(4880153153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1366263003/2500000000 : ℝ)*X 2 0+(4880153083/10000000000 : ℝ)*X 2 1+(-2173645937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4129335043/10000000000 : ℝ)*X 0 0+(3093273111/10000000000 : ℝ)*X 0 1+(1357141371/2500000000 : ℝ)*X 0 2+(4129335043/10000000000 : ℝ)*X 1 0+(3093273111/10000000000 : ℝ)*X 1 1+(1357141371/2500000000 : ℝ)*X 1 2+(4129335043/10000000000 : ℝ)*X 2 0+(3093273111/10000000000 : ℝ)*X 2 1+(1357141371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1627044089/10000000000 : ℝ)*X 0 0+(1226259931/2500000000 : ℝ)*X 0 1+(2921167321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1298742247/2500000000 : ℝ)*X 1 0+(-1211464781/10000000000 : ℝ)*X 1 1+(584233437/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((649371081/1250000000 : ℝ)*X 2 0+(233693397/400000000 : ℝ)*X 2 1+(-302866107/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1034129637/2500000000 : ℝ)*X 0 0+(5369738311/10000000000 : ℝ)*X 0 1+(197136361/625000000 : ℝ)*X 0 2+(1034129637/2500000000 : ℝ)*X 1 0+(5369738311/10000000000 : ℝ)*X 1 1+(197136361/625000000 : ℝ)*X 1 2+(1034129637/2500000000 : ℝ)*X 2 0+(5369738311/10000000000 : ℝ)*X 2 1+(197136361/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5904145380471545181/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5498297/10000000000000 : ℝ)*(base1) + (30195317/2500000000000 : ℝ)*(base19) + (304638777/25000000000000 : ℝ)*(base23) + (39288691/25000000000000 : ℝ)*(upper3) + (15621089/10000000000000 : ℝ)*(upper5) + (360105683960477/50000000000000 : ℝ)*(major0) + (360105683960477/50000000000000 : ℝ)*(major1) + (360105683960477/50000000000000 : ℝ)*(major2) + (506101195279739/50000000000000 : ℝ)*(sp0) + (31631426326417/3125000000000 : ℝ)*(sp1) + (253051407925729/25000000000000 : ℝ)*(sp2) + (107053429239873/25000000000000 : ℝ)*(sp3) + (902936303/20000000000000 : ℝ)*(sp4) + (239604571/12500000000000 : ℝ)*(sp7) + (42821568877903/10000000000000 : ℝ)*(f.failure) + (1012206850258023/100000000000000 : ℝ)*(f.sum) + (5289420857257/25000000000000000000000000000 : ℝ)*base66 + (208755481267743/50000000000000000000000000000 : ℝ)*base67 + (285814360267743/50000000000000000000000000000 : ℝ)*base69 + (156888963467743/50000000000000000000000000000 : ℝ)*base71 + (3073816832257/25000000000000000000000000000 : ℝ)*base74 + (187910283132257/50000000000000000000000000000 : ℝ)*base76 + (181555722667743/50000000000000000000000000000 : ℝ)*base77 + (100287171132257/50000000000000000000000000000 : ℝ)*base80 + (14873478167743/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4648911/500000000000000000000 : ℝ)*base90 + (4648911/500000000000000000000 : ℝ)*base92 + (4648911/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145910509715108078891751/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12164493/1000000000000 : ℝ)*(base19) + (1275043371/100000000000000 : ℝ)*(base23) + (66369689/50000000000000 : ℝ)*(base39) + (140653757/100000000000000 : ℝ)*(upper3) + (123440477/50000000000000 : ℝ)*(upper5) + (379563323169547/50000000000000 : ℝ)*(major0) + (379563323169547/50000000000000 : ℝ)*(major1) + (189781628399929/25000000000000 : ℝ)*(major2) + (3492954509/100000000000000 : ℝ)*(sp1) + (1726162943/50000000000000 : ℝ)*(sp2) + (1066899440285353/100000000000000 : ℝ)*(sp4) + (213378946176309/20000000000000 : ℝ)*(sp5) + (42675793826219/4000000000000 : ℝ)*(sp6) + (451353525106103/100000000000000 : ℝ)*(sp7) + (451353525106103/100000000000000 : ℝ)*(f.failure) + (266724893256183/25000000000000 : ℝ)*(f.sum) + (21003324572221/10000000000000000000000000000 : ℝ)*base66 + (136965666999989/25000000000000000000000000000 : ℝ)*base68 + (165420604538873/50000000000000000000000000000 : ℝ)*base69 + (126170939124989/25000000000000000000000000000 : ℝ)*base72 + (10081365022221/10000000000000000000000000000 : ℝ)*base74 + (481430390511127/50000000000000000000000000000 : ℝ)*base76 + (283576961561127/50000000000000000000000000000 : ℝ)*base78 + (587904665061127/50000000000000000000000000000 : ℝ)*base80 + (79244221088873/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (49807689/5000000000000000000000 : ℝ)*base89 + (49807689/5000000000000000000000 : ℝ)*base91 + (49807689/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1572_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1572_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1572_s1_0 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-440526331/2500000000 : ℝ)*x 0 + (5533701281/10000000000 : ℝ)*x 1 + (25627657/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440526331/2500000000 : ℝ)^4641 ≤ (10778983153457/100000000000000 : ℝ)^3617 := by
    have hnat : (440526331 : ℕ)^4641*100000000000000^3617 ≤ 10778983153457^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440526331 2500000000 10778983153457 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5533701281/10000000000 : ℝ)^4641 ≤ (46801688284249/100000000000000 : ℝ)^3617 := by
    have hnat : (5533701281 : ℕ)^4641*100000000000000^3617 ≤ 46801688284249^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5533701281 10000000000 46801688284249 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25627657/50000000 : ℝ)^4641 ≤ (530241606797/1250000000000 : ℝ)^3617 := by
    have hnat : (25627657 : ℕ)^4641*1250000000000^3617 ≤ 530241606797^3617*50000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25627657 50000000 530241606797 1250000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440526331/2500000000 : ℝ), (5533701281/10000000000 : ℝ), (25627657/50000000 : ℝ)] ![(10778983153457/100000000000000 : ℝ), (46801688284249/100000000000000 : ℝ), (530241606797/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440526331/2500000000 : ℝ)|^4641 ≤ (10778983153457/100000000000000 : ℝ)^3617
        have hw : |(-440526331/2500000000 : ℝ)|=(440526331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5533701281/10000000000 : ℝ)|^4641 ≤ (46801688284249/100000000000000 : ℝ)^3617
        have hw : |(5533701281/10000000000 : ℝ)|=(5533701281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25627657/50000000 : ℝ)|^4641 ≤ (530241606797/1250000000000 : ℝ)^3617
        have hw : |(25627657/50000000 : ℝ)|=(25627657/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s1_1 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688050473/5000000000 : ℝ)*x 0 + (-1975561657/10000000000 : ℝ)*x 1 + (640691389/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688050473/5000000000 : ℝ)^4641 ≤ (2254917774131/5000000000000 : ℝ)^3617 := by
    have hnat : (2688050473 : ℕ)^4641*5000000000000^3617 ≤ 2254917774131^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688050473 5000000000 2254917774131 5000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975561657/10000000000 : ℝ)^4641 ≤ (12482319026187/100000000000000 : ℝ)^3617 := by
    have hnat : (1975561657 : ℕ)^4641*100000000000000^3617 ≤ 12482319026187^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975561657 10000000000 12482319026187 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640691389/1250000000 : ℝ)^4641 ≤ (42419325485457/100000000000000 : ℝ)^3617 := by
    have hnat : (640691389 : ℕ)^4641*100000000000000^3617 ≤ 42419325485457^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640691389 1250000000 42419325485457 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688050473/5000000000 : ℝ), (-1975561657/10000000000 : ℝ), (640691389/1250000000 : ℝ)] ![(2254917774131/5000000000000 : ℝ), (12482319026187/100000000000000 : ℝ), (42419325485457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688050473/5000000000 : ℝ)|^4641 ≤ (2254917774131/5000000000000 : ℝ)^3617
        have hw : |(2688050473/5000000000 : ℝ)|=(2688050473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1975561657/10000000000 : ℝ)|^4641 ≤ (12482319026187/100000000000000 : ℝ)^3617
        have hw : |(-1975561657/10000000000 : ℝ)|=(1975561657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640691389/1250000000 : ℝ)|^4641 ≤ (42419325485457/100000000000000 : ℝ)^3617
        have hw : |(640691389/1250000000 : ℝ)|=(640691389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s1_2 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075220169/2000000000 : ℝ)*x 0 + (512553137/1000000000 : ℝ)*x 1 + (-493890363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075220169/2000000000 : ℝ)^4641 ≤ (45098354395499/100000000000000 : ℝ)^3617 := by
    have hnat : (1075220169 : ℕ)^4641*100000000000000^3617 ≤ 45098354395499^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075220169 2000000000 45098354395499 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512553137/1000000000 : ℝ)^4641 ≤ (42419328225187/100000000000000 : ℝ)^3617 := by
    have hnat : (512553137 : ℕ)^4641*100000000000000^3617 ≤ 42419328225187^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512553137 1000000000 42419328225187 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493890363/2500000000 : ℝ)^4641 ≤ (12482317364223/100000000000000 : ℝ)^3617 := by
    have hnat : (493890363 : ℕ)^4641*100000000000000^3617 ≤ 12482317364223^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493890363 2500000000 12482317364223 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075220169/2000000000 : ℝ), (512553137/1000000000 : ℝ), (-493890363/2500000000 : ℝ)] ![(45098354395499/100000000000000 : ℝ), (42419328225187/100000000000000 : ℝ), (12482317364223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075220169/2000000000 : ℝ)|^4641 ≤ (45098354395499/100000000000000 : ℝ)^3617
        have hw : |(1075220169/2000000000 : ℝ)|=(1075220169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512553137/1000000000 : ℝ)|^4641 ≤ (42419328225187/100000000000000 : ℝ)^3617
        have hw : |(512553137/1000000000 : ℝ)|=(512553137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493890363/2500000000 : ℝ)|^4641 ≤ (12482317364223/100000000000000 : ℝ)^3617
        have hw : |(-493890363/2500000000 : ℝ)|=(493890363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s1_3 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4227731867/10000000000 : ℝ)*x 0 + (3767471977/10000000000 : ℝ)*x 1 + (473229659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227731867/10000000000 : ℝ)^4641 ≤ (6626521694339/20000000000000 : ℝ)^3617 := by
    have hnat : (4227731867 : ℕ)^4641*20000000000000^3617 ≤ 6626521694339^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227731867 10000000000 6626521694339 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3767471977/10000000000 : ℝ)^4641 ≤ (7144413840883/25000000000000 : ℝ)^3617 := by
    have hnat : (3767471977 : ℕ)^4641*25000000000000^3617 ≤ 7144413840883^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3767471977 10000000000 7144413840883 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473229659/1000000000 : ℝ)^4641 ≤ (306317889263/800000000000 : ℝ)^3617 := by
    have hnat : (473229659 : ℕ)^4641*800000000000^3617 ≤ 306317889263^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473229659 1000000000 306317889263 800000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227731867/10000000000 : ℝ), (3767471977/10000000000 : ℝ), (473229659/1000000000 : ℝ)] ![(6626521694339/20000000000000 : ℝ), (7144413840883/25000000000000 : ℝ), (306317889263/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227731867/10000000000 : ℝ)|^4641 ≤ (6626521694339/20000000000000 : ℝ)^3617
        have hw : |(4227731867/10000000000 : ℝ)|=(4227731867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3767471977/10000000000 : ℝ)|^4641 ≤ (7144413840883/25000000000000 : ℝ)^3617
        have hw : |(3767471977/10000000000 : ℝ)|=(3767471977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(473229659/1000000000 : ℝ)|^4641 ≤ (306317889263/800000000000 : ℝ)^3617
        have hw : |(473229659/1000000000 : ℝ)|=(473229659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s1_4 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1762314029/10000000000 : ℝ)*x 0 + (5129730843/10000000000 : ℝ)*x 1 + (276472003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1762314029/10000000000 : ℝ)^4641 ≤ (431224851453/4000000000000 : ℝ)^3617 := by
    have hnat : (1762314029 : ℕ)^4641*4000000000000^3617 ≤ 431224851453^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762314029 10000000000 431224851453 4000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129730843/10000000000 : ℝ)^4641 ≤ (21231964022271/50000000000000 : ℝ)^3617 := by
    have hnat : (5129730843 : ℕ)^4641*50000000000000^3617 ≤ 21231964022271^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129730843 10000000000 21231964022271 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276472003/500000000 : ℝ)^4641 ≤ (46755450653147/100000000000000 : ℝ)^3617 := by
    have hnat : (276472003 : ℕ)^4641*100000000000000^3617 ≤ 46755450653147^3617*500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276472003 500000000 46755450653147 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1762314029/10000000000 : ℝ), (5129730843/10000000000 : ℝ), (276472003/500000000 : ℝ)] ![(431224851453/4000000000000 : ℝ), (21231964022271/50000000000000 : ℝ), (46755450653147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1762314029/10000000000 : ℝ)|^4641 ≤ (431224851453/4000000000000 : ℝ)^3617
        have hw : |(-1762314029/10000000000 : ℝ)|=(1762314029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129730843/10000000000 : ℝ)|^4641 ≤ (21231964022271/50000000000000 : ℝ)^3617
        have hw : |(5129730843/10000000000 : ℝ)|=(5129730843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276472003/500000000 : ℝ)|^4641 ≤ (46755450653147/100000000000000 : ℝ)^3617
        have hw : |(276472003/500000000 : ℝ)|=(276472003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s1_5 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267886357/10000000000 : ℝ)*x 0 + (-1571652687/10000000000 : ℝ)*x 1 + (691180069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267886357/10000000000 : ℝ)^4641 ≤ (21968457530007/50000000000000 : ℝ)^3617 := by
    have hnat : (5267886357 : ℕ)^4641*50000000000000^3617 ≤ 21968457530007^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267886357 10000000000 21968457530007 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1571652687/10000000000 : ℝ)^4641 ≤ (4653814470647/50000000000000 : ℝ)^3617 := by
    have hnat : (1571652687 : ℕ)^4641*50000000000000^3617 ≤ 4653814470647^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571652687 10000000000 4653814470647 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691180069/1250000000 : ℝ)^4641 ≤ (11688863997789/25000000000000 : ℝ)^3617 := by
    have hnat : (691180069 : ℕ)^4641*25000000000000^3617 ≤ 11688863997789^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691180069 1250000000 11688863997789 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267886357/10000000000 : ℝ), (-1571652687/10000000000 : ℝ), (691180069/1250000000 : ℝ)] ![(21968457530007/50000000000000 : ℝ), (4653814470647/50000000000000 : ℝ), (11688863997789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267886357/10000000000 : ℝ)|^4641 ≤ (21968457530007/50000000000000 : ℝ)^3617
        have hw : |(5267886357/10000000000 : ℝ)|=(5267886357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1571652687/10000000000 : ℝ)|^4641 ≤ (4653814470647/50000000000000 : ℝ)^3617
        have hw : |(-1571652687/10000000000 : ℝ)|=(1571652687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(691180069/1250000000 : ℝ)|^4641 ≤ (11688863997789/25000000000000 : ℝ)^3617
        have hw : |(691180069/1250000000 : ℝ)|=(691180069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s1_6 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164621431/312500000 : ℝ)*x 0 + (5529440763/10000000000 : ℝ)*x 1 + (-1571653181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164621431/312500000 : ℝ)^4641 ≤ (21968454506753/50000000000000 : ℝ)^3617 := by
    have hnat : (164621431 : ℕ)^4641*50000000000000^3617 ≤ 21968454506753^3617*312500000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164621431 312500000 21968454506753 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529440763/10000000000 : ℝ)^4641 ≤ (5844432285053/12500000000000 : ℝ)^3617 := by
    have hnat : (5529440763 : ℕ)^4641*12500000000000^3617 ≤ 5844432285053^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529440763 10000000000 5844432285053 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1571653181/10000000000 : ℝ)^4641 ≤ (4653816347553/50000000000000 : ℝ)^3617 := by
    have hnat : (1571653181 : ℕ)^4641*50000000000000^3617 ≤ 4653816347553^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571653181 10000000000 4653816347553 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164621431/312500000 : ℝ), (5529440763/10000000000 : ℝ), (-1571653181/10000000000 : ℝ)] ![(21968454506753/50000000000000 : ℝ), (5844432285053/12500000000000 : ℝ), (4653816347553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164621431/312500000 : ℝ)|^4641 ≤ (21968454506753/50000000000000 : ℝ)^3617
        have hw : |(164621431/312500000 : ℝ)|=(164621431/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529440763/10000000000 : ℝ)|^4641 ≤ (5844432285053/12500000000000 : ℝ)^3617
        have hw : |(5529440763/10000000000 : ℝ)|=(5529440763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1571653181/10000000000 : ℝ)|^4641 ≤ (4653816347553/50000000000000 : ℝ)^3617
        have hw : |(-1571653181/10000000000 : ℝ)|=(1571653181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s1_7 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057056037/2500000000 : ℝ)*x 0 + (4722370341/10000000000 : ℝ)*x 1 + (3777544527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057056037/2500000000 : ℝ)^4641 ≤ (16568779385653/50000000000000 : ℝ)^3617 := by
    have hnat : (1057056037 : ℕ)^4641*50000000000000^3617 ≤ 16568779385653^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057056037 2500000000 16568779385653 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4722370341/10000000000 : ℝ)^4641 ≤ (477333928061/1250000000000 : ℝ)^3617 := by
    have hnat : (4722370341 : ℕ)^4641*1250000000000^3617 ≤ 477333928061^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4722370341 10000000000 477333928061 1250000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3777544527/10000000000 : ℝ)^4641 ≤ (28675726967683/100000000000000 : ℝ)^3617 := by
    have hnat : (3777544527 : ℕ)^4641*100000000000000^3617 ≤ 28675726967683^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3777544527 10000000000 28675726967683 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057056037/2500000000 : ℝ), (4722370341/10000000000 : ℝ), (3777544527/10000000000 : ℝ)] ![(16568779385653/50000000000000 : ℝ), (477333928061/1250000000000 : ℝ), (28675726967683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057056037/2500000000 : ℝ)|^4641 ≤ (16568779385653/50000000000000 : ℝ)^3617
        have hw : |(1057056037/2500000000 : ℝ)|=(1057056037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4722370341/10000000000 : ℝ)|^4641 ≤ (477333928061/1250000000000 : ℝ)^3617
        have hw : |(4722370341/10000000000 : ℝ)|=(4722370341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3777544527/10000000000 : ℝ)|^4641 ≤ (28675726967683/100000000000000 : ℝ)^3617
        have hw : |(3777544527/10000000000 : ℝ)|=(3777544527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1572_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2273/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17737/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (223/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (223/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (223/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (223/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (223/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (223/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (223/6250 : ℝ) ^ (4639/1024 : ℝ) ≤ (6918767526643/25000000000000000000 : ℝ) := by
    have hpowers : (223/6250 : ℝ)^4639 ≤ (6918767526643/25000000000000000000 : ℝ)^1024 := by
      have hnat : (223 : ℕ)^4639*25000000000000000000^1024 ≤ 6918767526643^1024*6250^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 6250 6918767526643 25000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/6250 : ℝ)) (X := (6918767526643/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2473/10000 : ℝ) ^ (4639/1024 : ℝ) ≤ (89147534400870947/50000000000000000000 : ℝ) := by
    have hpowers : (2473/10000 : ℝ)^4639 ≤ (89147534400870947/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2473 : ℕ)^4639*50000000000000000000^1024 ≤ 89147534400870947^1024*10000^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2473 10000 89147534400870947 50000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2473/10000 : ℝ)) (X := (89147534400870947/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500006918767526643/12500000000000000000 : ℝ) ≤ (2500000305445847/2500000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (12500006918767526643/12500000000000000000 : ℝ)^1024 ≤ (2500000305445847/2500000000000000 : ℝ)^4639 := by
      have hnat : (12500006918767526643 : ℕ)^1024*2500000000000000^4639 ≤ 2500000305445847^4639*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500006918767526643 12500000000000000000 2500000305445847 2500000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000305445847/2500000000000000 : ℝ)) (X := (12500006918767526643/12500000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50089161371935924233/50000000000000000000 : ℝ) ≤ (10003933514793679/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (50089161371935924233/50000000000000000000 : ℝ)^1024 ≤ (10003933514793679/10000000000000000 : ℝ)^4639 := by
      have hnat : (50089161371935924233 : ℕ)^1024*10000000000000000^4639 ≤ 10003933514793679^4639*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50089161371935924233 50000000000000000000 10003933514793679 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003933514793679/10000000000000000 : ℝ)) (X := (50089161371935924233/50000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25089147534400870947/25000000000000000000 : ℝ) ≤ (1000786580780397/1000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (25089147534400870947/25000000000000000000 : ℝ)^1024 ≤ (1000786580780397/1000000000000000 : ℝ)^4639 := by
      have hnat : (25089147534400870947 : ℕ)^1024*1000000000000000^4639 ≤ 1000786580780397^4639*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25089147534400870947 25000000000000000000 1000786580780397 1000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000786580780397/1000000000000000 : ℝ)) (X := (25089147534400870947/25000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6918767526643/25000000000000000000 : ℝ) ≤ ((5289799125311465507/5290500000000000000 : ℝ)+2*(3932293010291/2116200000000000 : ℝ)*(223/6250 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (5289799125311465507/5290500000000000000 : ℝ)+2*(3932293010291/2116200000000000 : ℝ)*(223/6250 : ℝ)=(2500000305445847/2500000000000000 : ℝ) by norm_num, show 1+2*(6918767526643/25000000000000000000 : ℝ)=(12500006918767526643/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(89147534400870947/50000000000000000000 : ℝ)+(6918767526643/25000000000000000000 : ℝ) ≤ ((5289799125311465507/5290500000000000000 : ℝ)+(3932293010291/2116200000000000 : ℝ)*((2473/10000 : ℝ)+(223/6250 : ℝ)))^(4639/1024 : ℝ) := by
    rw [show (5289799125311465507/5290500000000000000 : ℝ)+(3932293010291/2116200000000000 : ℝ)*((2473/10000 : ℝ)+(223/6250 : ℝ))=(10003933514793679/10000000000000000 : ℝ) by norm_num, show 1+(89147534400870947/50000000000000000000 : ℝ)+(6918767526643/25000000000000000000 : ℝ)=(50089161371935924233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(89147534400870947/50000000000000000000 : ℝ) ≤ ((5289799125311465507/5290500000000000000 : ℝ)+2*(3932293010291/2116200000000000 : ℝ)*(2473/10000 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (5289799125311465507/5290500000000000000 : ℝ)+2*(3932293010291/2116200000000000 : ℝ)*(2473/10000 : ℝ)=(1000786580780397/1000000000000000 : ℝ) by norm_num, show 1+2*(89147534400870947/50000000000000000000 : ℝ)=(25089147534400870947/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5289799125311465507/5290500000000000000 : ℝ)*(X 1 0+X 2 0)+(3932293010291/2116200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (223/6250 : ℝ)) (hi := (2473/10000 : ℝ)) (c := (5289799125311465507/5290500000000000000 : ℝ)) (alpha := (3932293010291/2116200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5289799125311465507/5290500000000000000 : ℝ)*(X 0 1+X 2 1)+(3932293010291/2116200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (223/6250 : ℝ)) (hi := (2473/10000 : ℝ)) (c := (5289799125311465507/5290500000000000000 : ℝ)) (alpha := (3932293010291/2116200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5289799125311465507/5290500000000000000 : ℝ)*(X 0 2+X 1 2)+(3932293010291/2116200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (223/6250 : ℝ)) (hi := (2473/10000 : ℝ)) (c := (5289799125311465507/5290500000000000000 : ℝ)) (alpha := (3932293010291/2116200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-440526331/2500000000 : ℝ)*X 0 0+(5533701281/10000000000 : ℝ)*X 0 1+(25627657/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688050473/5000000000 : ℝ)*X 1 0+(-1975561657/10000000000 : ℝ)*X 1 1+(640691389/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1075220169/2000000000 : ℝ)*X 2 0+(512553137/1000000000 : ℝ)*X 2 1+(-493890363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4227731867/10000000000 : ℝ)*X 0 0+(3767471977/10000000000 : ℝ)*X 0 1+(473229659/1000000000 : ℝ)*X 0 2+(4227731867/10000000000 : ℝ)*X 1 0+(3767471977/10000000000 : ℝ)*X 1 1+(473229659/1000000000 : ℝ)*X 1 2+(4227731867/10000000000 : ℝ)*X 2 0+(3767471977/10000000000 : ℝ)*X 2 1+(473229659/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1762314029/10000000000 : ℝ)*X 0 0+(5129730843/10000000000 : ℝ)*X 0 1+(276472003/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5267886357/10000000000 : ℝ)*X 1 0+(-1571652687/10000000000 : ℝ)*X 1 1+(691180069/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((164621431/312500000 : ℝ)*X 2 0+(5529440763/10000000000 : ℝ)*X 2 1+(-1571653181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1057056037/2500000000 : ℝ)*X 0 0+(4722370341/10000000000 : ℝ)*X 0 1+(3777544527/10000000000 : ℝ)*X 0 2+(1057056037/2500000000 : ℝ)*X 1 0+(4722370341/10000000000 : ℝ)*X 1 1+(3777544527/10000000000 : ℝ)*X 1 2+(1057056037/2500000000 : ℝ)*X 2 0+(4722370341/10000000000 : ℝ)*X 2 1+(3777544527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (207774039272455316727608801/88175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (474353/10000000000000 : ℝ)*(base1) + (998882351/100000000000000 : ℝ)*(base19) + (952855009/100000000000000 : ℝ)*(base23) + (1316779/5000000000000 : ℝ)*(upper3) + (67575289/50000000000000 : ℝ)*(upper5) + (1743222187568957/100000000000000 : ℝ)*(major0) + (1743222187568957/100000000000000 : ℝ)*(major1) + (1743222187568957/100000000000000 : ℝ)*(major2) + (2449968019681819/100000000000000 : ℝ)*(sp0) + (306247076460877/12500000000000 : ℝ)*(sp1) + (1224988328857179/50000000000000 : ℝ)*(sp2) + (1036462550775453/100000000000000 : ℝ)*(sp3) + (4797815539/50000000000000 : ℝ)*(sp4) + (413050347/10000000000000 : ℝ)*(sp7) + (518233343011227/50000000000000 : ℝ)*(f.failure) + (2449977610569367/100000000000000 : ℝ)*(f.sum) + (232953699450157/105810000000000000000000000000 : ℝ)*base65 + (824525480082516301/529050000000000000000000000000000 : ℝ)*base68 + (734477739408683699/529050000000000000000000000000000 : ℝ)*base69 + (1551206711904666301/529050000000000000000000000000000 : ℝ)*base72 + (241145109313103/105810000000000000000000000000 : ℝ)*base74 + (6899687576535083699/529050000000000000000000000000000 : ℝ)*base75 + (1390885109480633699/529050000000000000000000000000000 : ℝ)*base77 + (4175123162896133699/529050000000000000000000000000000 : ℝ)*base79 + (116359969760153/105810000000000000000000000000 : ℝ)*base82 + (12536101/2500000000000000000000 : ℝ)*base89 + (12536101/2500000000000000000000 : ℝ)*base91 + (12536101/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181504417681619915101439349/22043750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1454703317/100000000000000 : ℝ)*(base19) + (654740839/50000000000000 : ℝ)*(base23) + (7414597/10000000000000 : ℝ)*(upper2) + (71297201/25000000000000 : ℝ)*(upper3) + (142376557/100000000000000 : ℝ)*(upper5) + (890052831981843/50000000000000 : ℝ)*(major0) + (890052831981843/50000000000000 : ℝ)*(major1) + (890052831981843/50000000000000 : ℝ)*(major2) + (3021928869/25000000000000 : ℝ)*(sp1) + (1403595019/12500000000000 : ℝ)*(sp2) + (312726822320251/12500000000000 : ℝ)*(sp4) + (156362564758951/6250000000000 : ℝ)*(sp5) + (1250901020160089/50000000000000 : ℝ)*(sp6) + (1058396474904469/100000000000000 : ℝ)*(sp7) + (1058396474904469/100000000000000 : ℝ)*(f.failure) + (312726822320251/12500000000000 : ℝ)*(f.sum) + (50447572070529/17635000000000000000000000000 : ℝ)*base66 + (417464123911748967/88175000000000000000000000000000 : ℝ)*base67 + (386650050181998967/88175000000000000000000000000000 : ℝ)*base69 + (360300699325023967/88175000000000000000000000000000 : ℝ)*base71 + (4171436481851/4408750000000000000000000000 : ℝ)*base74 + (251978907661201033/88175000000000000000000000000000 : ℝ)*base76 + (243936591994623967/88175000000000000000000000000000 : ℝ)*base77 + (588437978652498967/88175000000000000000000000000000 : ℝ)*base79 + (2257596977579/1102187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3144853/5000000000000000000000 : ℝ)*base90 + (3144853/5000000000000000000000 : ℝ)*base92 + (3144853/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1572_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17737/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1572_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1572_s2_0 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1780522363/10000000000 : ℝ)*x 0 + (13602369/25000000 : ℝ)*x 1 + (5206281223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1780522363/10000000000 : ℝ)^4641 ≤ (1365468755971/12500000000000 : ℝ)^3617 := by
    have hnat : (1780522363 : ℕ)^4641*12500000000000^3617 ≤ 1365468755971^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780522363 10000000000 1365468755971 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13602369/25000000 : ℝ)^4641 ≤ (22898762666643/50000000000000 : ℝ)^3617 := by
    have hnat : (13602369 : ℕ)^4641*50000000000000^3617 ≤ 22898762666643^3617*25000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13602369 25000000 22898762666643 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206281223/10000000000 : ℝ)^4641 ≤ (10819681150623/25000000000000 : ℝ)^3617 := by
    have hnat : (5206281223 : ℕ)^4641*25000000000000^3617 ≤ 10819681150623^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206281223 10000000000 10819681150623 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1780522363/10000000000 : ℝ), (13602369/25000000 : ℝ), (5206281223/10000000000 : ℝ)] ![(1365468755971/12500000000000 : ℝ), (22898762666643/50000000000000 : ℝ), (10819681150623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1780522363/10000000000 : ℝ)|^4641 ≤ (1365468755971/12500000000000 : ℝ)^3617
        have hw : |(-1780522363/10000000000 : ℝ)|=(1780522363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13602369/25000000 : ℝ)|^4641 ≤ (22898762666643/50000000000000 : ℝ)^3617
        have hw : |(13602369/25000000 : ℝ)|=(13602369/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206281223/10000000000 : ℝ)|^4641 ≤ (10819681150623/25000000000000 : ℝ)^3617
        have hw : |(5206281223/10000000000 : ℝ)|=(5206281223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s2_1 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352132477/10000000000 : ℝ)*x 0 + (-1900956681/10000000000 : ℝ)*x 1 + (2603140349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352132477/10000000000 : ℝ)^4641 ≤ (44840532169789/100000000000000 : ℝ)^3617 := by
    have hnat : (5352132477 : ℕ)^4641*100000000000000^3617 ≤ 44840532169789^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352132477 10000000000 44840532169789 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1900956681/10000000000 : ℝ)^4641 ≤ (1188074880671/10000000000000 : ℝ)^3617 := by
    have hnat : (1900956681 : ℕ)^4641*10000000000000^3617 ≤ 1188074880671^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900956681 10000000000 1188074880671 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603140349/5000000000 : ℝ)^4641 ≤ (8655743800547/20000000000000 : ℝ)^3617 := by
    have hnat : (2603140349 : ℕ)^4641*20000000000000^3617 ≤ 8655743800547^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603140349 5000000000 8655743800547 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352132477/10000000000 : ℝ), (-1900956681/10000000000 : ℝ), (2603140349/5000000000 : ℝ)] ![(44840532169789/100000000000000 : ℝ), (1188074880671/10000000000000 : ℝ), (8655743800547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352132477/10000000000 : ℝ)|^4641 ≤ (44840532169789/100000000000000 : ℝ)^3617
        have hw : |(5352132477/10000000000 : ℝ)|=(5352132477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1900956681/10000000000 : ℝ)|^4641 ≤ (1188074880671/10000000000000 : ℝ)^3617
        have hw : |(-1900956681/10000000000 : ℝ)|=(1900956681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2603140349/5000000000 : ℝ)|^4641 ≤ (8655743800547/20000000000000 : ℝ)^3617
        have hw : |(2603140349/5000000000 : ℝ)|=(2603140349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s2_2 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676066511/5000000000 : ℝ)*x 0 + (208251213/400000000 : ℝ)*x 1 + (-1900956447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676066511/5000000000 : ℝ)^4641 ≤ (44840538028519/100000000000000 : ℝ)^3617 := by
    have hnat : (2676066511 : ℕ)^4641*100000000000000^3617 ≤ 44840538028519^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676066511 5000000000 44840538028519 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208251213/400000000 : ℝ)^4641 ≤ (43278715024241/100000000000000 : ℝ)^3617 := by
    have hnat : (208251213 : ℕ)^4641*100000000000000^3617 ≤ 43278715024241^3617*400000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208251213 400000000 43278715024241 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1900956447/10000000000 : ℝ)^4641 ≤ (5940373465101/50000000000000 : ℝ)^3617 := by
    have hnat : (1900956447 : ℕ)^4641*50000000000000^3617 ≤ 5940373465101^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900956447 10000000000 5940373465101 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676066511/5000000000 : ℝ), (208251213/400000000 : ℝ), (-1900956447/10000000000 : ℝ)] ![(44840538028519/100000000000000 : ℝ), (43278715024241/100000000000000 : ℝ), (5940373465101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676066511/5000000000 : ℝ)|^4641 ≤ (44840538028519/100000000000000 : ℝ)^3617
        have hw : |(2676066511/5000000000 : ℝ)|=(2676066511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208251213/400000000 : ℝ)|^4641 ≤ (43278715024241/100000000000000 : ℝ)^3617
        have hw : |(208251213/400000000 : ℝ)|=(208251213/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1900956447/10000000000 : ℝ)|^4641 ≤ (5940373465101/50000000000000 : ℝ)^3617
        have hw : |(-1900956447/10000000000 : ℝ)|=(1900956447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s2_3 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4241084511/10000000000 : ℝ)*x 0 + (248191401/625000000 : ℝ)*x 1 + (2262881391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4241084511/10000000000 : ℝ)^4641 ≤ (3326693831119/10000000000000 : ℝ)^3617 := by
    have hnat : (4241084511 : ℕ)^4641*10000000000000^3617 ≤ 3326693831119^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241084511 10000000000 3326693831119 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248191401/625000000 : ℝ)^4641 ≤ (30574134827349/100000000000000 : ℝ)^3617 := by
    have hnat : (248191401 : ℕ)^4641*100000000000000^3617 ≤ 30574134827349^3617*625000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248191401 625000000 30574134827349 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262881391/5000000000 : ℝ)^4641 ≤ (4519865856543/12500000000000 : ℝ)^3617 := by
    have hnat : (2262881391 : ℕ)^4641*12500000000000^3617 ≤ 4519865856543^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262881391 5000000000 4519865856543 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4241084511/10000000000 : ℝ), (248191401/625000000 : ℝ), (2262881391/5000000000 : ℝ)] ![(3326693831119/10000000000000 : ℝ), (30574134827349/100000000000000 : ℝ), (4519865856543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4241084511/10000000000 : ℝ)|^4641 ≤ (3326693831119/10000000000000 : ℝ)^3617
        have hw : |(4241084511/10000000000 : ℝ)|=(4241084511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(248191401/625000000 : ℝ)|^4641 ≤ (30574134827349/100000000000000 : ℝ)^3617
        have hw : |(248191401/625000000 : ℝ)|=(248191401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262881391/5000000000 : ℝ)|^4641 ≤ (4519865856543/12500000000000 : ℝ)^3617
        have hw : |(2262881391/5000000000 : ℝ)|=(2262881391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s2_4 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1780561767/10000000000 : ℝ)*x 0 + (1041535409/2000000000 : ℝ)*x 1 + (5439540267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1780561767/10000000000 : ℝ)^4641 ≤ (10924060238667/100000000000000 : ℝ)^3617 := by
    have hnat : (1780561767 : ℕ)^4641*100000000000000^3617 ≤ 10924060238667^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780561767 10000000000 10924060238667 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041535409/2000000000 : ℝ)^4641 ≤ (43293613289833/100000000000000 : ℝ)^3617 := by
    have hnat : (1041535409 : ℕ)^4641*100000000000000^3617 ≤ 43293613289833^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041535409 2000000000 43293613289833 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439540267/10000000000 : ℝ)^4641 ≤ (45782326456411/100000000000000 : ℝ)^3617 := by
    have hnat : (5439540267 : ℕ)^4641*100000000000000^3617 ≤ 45782326456411^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439540267 10000000000 45782326456411 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1780561767/10000000000 : ℝ), (1041535409/2000000000 : ℝ), (5439540267/10000000000 : ℝ)] ![(10924060238667/100000000000000 : ℝ), (43293613289833/100000000000000 : ℝ), (45782326456411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1780561767/10000000000 : ℝ)|^4641 ≤ (10924060238667/100000000000000 : ℝ)^3617
        have hw : |(-1780561767/10000000000 : ℝ)|=(1780561767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041535409/2000000000 : ℝ)|^4641 ≤ (43293613289833/100000000000000 : ℝ)^3617
        have hw : |(1041535409/2000000000 : ℝ)|=(1041535409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439540267/10000000000 : ℝ)|^4641 ≤ (45782326456411/100000000000000 : ℝ)^3617
        have hw : |(5439540267/10000000000 : ℝ)|=(5439540267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s2_5 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322506433/2500000000 : ℝ)*x 0 + (-333539451/2000000000 : ℝ)*x 1 + (5439541201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322506433/2500000000 : ℝ)^4641 ≤ (22086993351411/50000000000000 : ℝ)^3617 := by
    have hnat : (1322506433 : ℕ)^4641*50000000000000^3617 ≤ 22086993351411^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322506433 2500000000 22086993351411 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (333539451/2000000000 : ℝ)^4641 ≤ (5021838365897/50000000000000 : ℝ)^3617 := by
    have hnat : (333539451 : ℕ)^4641*50000000000000^3617 ≤ 5021838365897^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333539451 2000000000 5021838365897 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439541201/10000000000 : ℝ)^4641 ≤ (4578233654303/10000000000000 : ℝ)^3617 := by
    have hnat : (5439541201 : ℕ)^4641*10000000000000^3617 ≤ 4578233654303^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439541201 10000000000 4578233654303 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322506433/2500000000 : ℝ), (-333539451/2000000000 : ℝ), (5439541201/10000000000 : ℝ)] ![(22086993351411/50000000000000 : ℝ), (5021838365897/50000000000000 : ℝ), (4578233654303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322506433/2500000000 : ℝ)|^4641 ≤ (22086993351411/50000000000000 : ℝ)^3617
        have hw : |(1322506433/2500000000 : ℝ)|=(1322506433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-333539451/2000000000 : ℝ)|^4641 ≤ (5021838365897/50000000000000 : ℝ)^3617
        have hw : |(-333539451/2000000000 : ℝ)|=(333539451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439541201/10000000000 : ℝ)|^4641 ≤ (4578233654303/10000000000000 : ℝ)^3617
        have hw : |(5439541201/10000000000 : ℝ)|=(5439541201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s2_6 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290026099/10000000000 : ℝ)*x 0 + (5439542289/10000000000 : ℝ)*x 1 + (-1667695227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290026099/10000000000 : ℝ)^4641 ≤ (44173990635043/100000000000000 : ℝ)^3617 := by
    have hnat : (5290026099 : ℕ)^4641*100000000000000^3617 ≤ 44173990635043^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290026099 10000000000 44173990635043 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439542289/10000000000 : ℝ)^4641 ≤ (22891174146377/50000000000000 : ℝ)^3617 := by
    have hnat : (5439542289 : ℕ)^4641*50000000000000^3617 ≤ 22891174146377^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439542289 10000000000 22891174146377 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1667695227/10000000000 : ℝ)^4641 ≤ (10043661060443/100000000000000 : ℝ)^3617 := by
    have hnat : (1667695227 : ℕ)^4641*100000000000000^3617 ≤ 10043661060443^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667695227 10000000000 10043661060443 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290026099/10000000000 : ℝ), (5439542289/10000000000 : ℝ), (-1667695227/10000000000 : ℝ)] ![(44173990635043/100000000000000 : ℝ), (22891174146377/50000000000000 : ℝ), (10043661060443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290026099/10000000000 : ℝ)|^4641 ≤ (44173990635043/100000000000000 : ℝ)^3617
        have hw : |(5290026099/10000000000 : ℝ)|=(5290026099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439542289/10000000000 : ℝ)|^4641 ≤ (22891174146377/50000000000000 : ℝ)^3617
        have hw : |(5439542289/10000000000 : ℝ)|=(5439542289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1667695227/10000000000 : ℝ)|^4641 ≤ (10043661060443/100000000000000 : ℝ)^3617
        have hw : |(-1667695227/10000000000 : ℝ)|=(1667695227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s2_7 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848235631/2000000000 : ℝ)*x 0 + (4522463853/10000000000 : ℝ)*x 1 + (993597399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848235631/2000000000 : ℝ)^4641 ≤ (33267880808847/100000000000000 : ℝ)^3617 := by
    have hnat : (848235631 : ℕ)^4641*100000000000000^3617 ≤ 33267880808847^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848235631 2000000000 33267880808847 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522463853/10000000000 : ℝ)^4641 ≤ (36125111419327/100000000000000 : ℝ)^3617 := by
    have hnat : (4522463853 : ℕ)^4641*100000000000000^3617 ≤ 36125111419327^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522463853 10000000000 36125111419327 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (993597399/2500000000 : ℝ)^4641 ≤ (15303503874867/50000000000000 : ℝ)^3617 := by
    have hnat : (993597399 : ℕ)^4641*50000000000000^3617 ≤ 15303503874867^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993597399 2500000000 15303503874867 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848235631/2000000000 : ℝ), (4522463853/10000000000 : ℝ), (993597399/2500000000 : ℝ)] ![(33267880808847/100000000000000 : ℝ), (36125111419327/100000000000000 : ℝ), (15303503874867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848235631/2000000000 : ℝ)|^4641 ≤ (33267880808847/100000000000000 : ℝ)^3617
        have hw : |(848235631/2000000000 : ℝ)|=(848235631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522463853/10000000000 : ℝ)|^4641 ≤ (36125111419327/100000000000000 : ℝ)^3617
        have hw : |(4522463853/10000000000 : ℝ)|=(4522463853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(993597399/2500000000 : ℝ)|^4641 ≤ (15303503874867/50000000000000 : ℝ)^3617
        have hw : |(993597399/2500000000 : ℝ)|=(993597399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1572_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10831/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7903/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2273/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2273/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2273/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2273/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2273/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2273/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2273/25000 : ℝ) ^ (4639/1024 : ℝ) ≤ (958103589688817/50000000000000000000 : ℝ) := by
    have hpowers : (2273/25000 : ℝ)^4639 ≤ (958103589688817/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2273 : ℕ)^4639*50000000000000000000^1024 ≤ 958103589688817^1024*25000^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 25000 958103589688817 50000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/25000 : ℝ)) (X := (958103589688817/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17737/100000 : ℝ) ^ (4639/1024 : ℝ) ≤ (39556856129383907/100000000000000000000 : ℝ) := by
    have hpowers : (17737/100000 : ℝ)^4639 ≤ (39556856129383907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17737 : ℕ)^4639*100000000000000000000^1024 ≤ 39556856129383907^1024*100000^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17737 100000 39556856129383907 100000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17737/100000 : ℝ)) (X := (39556856129383907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000958103589688817/25000000000000000000 : ℝ) ≤ (400003383775559/400000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (25000958103589688817/25000000000000000000 : ℝ)^1024 ≤ (400003383775559/400000000000000 : ℝ)^4639 := by
      have hnat : (25000958103589688817 : ℕ)^1024*400000000000000^4639 ≤ 400003383775559^4639*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000958103589688817 25000000000000000000 400003383775559 400000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400003383775559/400000000000000 : ℝ)) (X := (25000958103589688817/25000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041473063308761541/100000000000000000000 : ℝ) ≤ (10000915317007033/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (100041473063308761541/100000000000000000000 : ℝ)^1024 ≤ (10000915317007033/10000000000000000 : ℝ)^4639 := by
      have hnat : (100041473063308761541 : ℕ)^1024*10000000000000000^4639 ≤ 10000915317007033^4639*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041473063308761541 100000000000000000000 10000915317007033 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000915317007033/10000000000000000 : ℝ)) (X := (100041473063308761541/100000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039556856129383907/50000000000000000000 : ℝ) ≤ (10001746039625091/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (50039556856129383907/50000000000000000000 : ℝ)^1024 ≤ (10001746039625091/10000000000000000 : ℝ)^4639 := by
      have hnat : (50039556856129383907 : ℕ)^1024*10000000000000000^4639 ≤ 10001746039625091^4639*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039556856129383907 50000000000000000000 10001746039625091 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001746039625091/10000000000000000 : ℝ)) (X := (50039556856129383907/50000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(958103589688817/50000000000000000000 : ℝ) ≤ ((86435625458405922203/86450000000000000000 : ℝ)+2*(415361309029/432250000000000 : ℝ)*(2273/25000 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (86435625458405922203/86450000000000000000 : ℝ)+2*(415361309029/432250000000000 : ℝ)*(2273/25000 : ℝ)=(400003383775559/400000000000000 : ℝ) by norm_num, show 1+2*(958103589688817/50000000000000000000 : ℝ)=(25000958103589688817/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39556856129383907/100000000000000000000 : ℝ)+(958103589688817/50000000000000000000 : ℝ) ≤ ((86435625458405922203/86450000000000000000 : ℝ)+(415361309029/432250000000000 : ℝ)*((17737/100000 : ℝ)+(2273/25000 : ℝ)))^(4639/1024 : ℝ) := by
    rw [show (86435625458405922203/86450000000000000000 : ℝ)+(415361309029/432250000000000 : ℝ)*((17737/100000 : ℝ)+(2273/25000 : ℝ))=(10000915317007033/10000000000000000 : ℝ) by norm_num, show 1+(39556856129383907/100000000000000000000 : ℝ)+(958103589688817/50000000000000000000 : ℝ)=(100041473063308761541/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39556856129383907/100000000000000000000 : ℝ) ≤ ((86435625458405922203/86450000000000000000 : ℝ)+2*(415361309029/432250000000000 : ℝ)*(17737/100000 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (86435625458405922203/86450000000000000000 : ℝ)+2*(415361309029/432250000000000 : ℝ)*(17737/100000 : ℝ)=(10001746039625091/10000000000000000 : ℝ) by norm_num, show 1+2*(39556856129383907/100000000000000000000 : ℝ)=(50039556856129383907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (86435625458405922203/86450000000000000000 : ℝ)*(X 1 0+X 2 0)+(415361309029/432250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (2273/25000 : ℝ)) (hi := (17737/100000 : ℝ)) (c := (86435625458405922203/86450000000000000000 : ℝ)) (alpha := (415361309029/432250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (86435625458405922203/86450000000000000000 : ℝ)*(X 0 1+X 2 1)+(415361309029/432250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (2273/25000 : ℝ)) (hi := (17737/100000 : ℝ)) (c := (86435625458405922203/86450000000000000000 : ℝ)) (alpha := (415361309029/432250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (86435625458405922203/86450000000000000000 : ℝ)*(X 0 2+X 1 2)+(415361309029/432250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (2273/25000 : ℝ)) (hi := (17737/100000 : ℝ)) (c := (86435625458405922203/86450000000000000000 : ℝ)) (alpha := (415361309029/432250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1780522363/10000000000 : ℝ)*X 0 0+(13602369/25000000 : ℝ)*X 0 1+(5206281223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352132477/10000000000 : ℝ)*X 1 0+(-1900956681/10000000000 : ℝ)*X 1 1+(2603140349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676066511/5000000000 : ℝ)*X 2 0+(208251213/400000000 : ℝ)*X 2 1+(-1900956447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4241084511/10000000000 : ℝ)*X 0 0+(248191401/625000000 : ℝ)*X 0 1+(2262881391/5000000000 : ℝ)*X 0 2+(4241084511/10000000000 : ℝ)*X 1 0+(248191401/625000000 : ℝ)*X 1 1+(2262881391/5000000000 : ℝ)*X 1 2+(4241084511/10000000000 : ℝ)*X 2 0+(248191401/625000000 : ℝ)*X 2 1+(2262881391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1780561767/10000000000 : ℝ)*X 0 0+(1041535409/2000000000 : ℝ)*X 0 1+(5439540267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322506433/2500000000 : ℝ)*X 1 0+(-333539451/2000000000 : ℝ)*X 1 1+(5439541201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290026099/10000000000 : ℝ)*X 2 0+(5439542289/10000000000 : ℝ)*X 2 1+(-1667695227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((848235631/2000000000 : ℝ)*X 0 0+(4522463853/10000000000 : ℝ)*X 0 1+(993597399/2500000000 : ℝ)*X 0 2+(848235631/2000000000 : ℝ)*X 1 0+(4522463853/10000000000 : ℝ)*X 1 1+(993597399/2500000000 : ℝ)*X 1 2+(848235631/2000000000 : ℝ)*X 2 0+(4522463853/10000000000 : ℝ)*X 2 1+(993597399/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1157033517436918698713505567/166250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (804084689/100000000000000 : ℝ)*(base19) + (248842287/25000000000000 : ℝ)*(base23) + (5194669/4000000000000 : ℝ)*(lower2) + (46527061/100000000000000 : ℝ)*(upper3) + (36136457/25000000000000 : ℝ)*(upper5) + (3032075796715219/100000000000000 : ℝ)*(major0) + (3032075796715219/100000000000000 : ℝ)*(major1) + (3032075796715219/100000000000000 : ℝ)*(major2) + (4261366733661521/100000000000000 : ℝ)*(sp0) + (2130685434286563/50000000000000 : ℝ)*(sp1) + (2130685338644333/50000000000000 : ℝ)*(sp2) + (1802777028420527/100000000000000 : ℝ)*(sp3) + (2469498147/50000000000000 : ℝ)*(sp4) + (332545677/12500000000000 : ℝ)*(sp7) + (901389844392971/50000000000000 : ℝ)*(f.failure) + (2130685836328907/50000000000000 : ℝ)*(f.sum) + (89558754596699/21612500000000000000000000000 : ℝ)*base66 + (12970814122231384649/1235000000000000000000000000000000 : ℝ)*base68 + (10134929096166384649/1235000000000000000000000000000000 : ℝ)*base70 + (4085564593946384649/1235000000000000000000000000000000 : ℝ)*base72 + (70611794842237/10806250000000000000000000000 : ℝ)*base74 + (12726738710911384649/1235000000000000000000000000000000 : ℝ)*base76 + (2123045298196384649/1235000000000000000000000000000000 : ℝ)*base78 + (1058630737068615351/1235000000000000000000000000000000 : ℝ)*base79 + (156355410258799/21612500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (17780427/2500000000000000000000 : ℝ)*base90 + (17780427/2500000000000000000000 : ℝ)*base92 + (17780427/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15665643643928797639165833/5937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84794911/50000000000000 : ℝ)*(base8) + (426067419/50000000000000 : ℝ)*(base15) + (7263009/12500000000000 : ℝ)*(base29) + (8943969/50000000000000 : ℝ)*(lower2) + (39522733/100000000000000 : ℝ)*(lower4) + (383590939577029/12500000000000 : ℝ)*(major0) + (191795473420019/6250000000000 : ℝ)*(major1) + (191795473420019/6250000000000 : ℝ)*(major2) + (17826974277/50000000000000 : ℝ)*(sp2) + (12605501/781250000000 : ℝ)*(sp3) + (4312883175023259/100000000000000 : ℝ)*(sp4) + (1078220608593543/25000000000000 : ℝ)*(sp5) + (862569526512091/20000000000000 : ℝ)*(sp6) + (364914020675183/20000000000000 : ℝ)*(sp7) + (912285858440021/50000000000000 : ℝ)*(f.failure) + (4312883344613081/100000000000000 : ℝ)*(f.sum) + (17992051721281/1543750000000000000000000000 : ℝ)*base66 + (544815197909270449/77187500000000000000000000000000 : ℝ)*base68 + (615015005464582949/77187500000000000000000000000000 : ℝ)*base70 + (18710348840425350113/1080625000000000000000000000000000 : ℝ)*base72 + (73153916159131/43225000000000000000000000000 : ℝ)*base74 + (4193002114844118143/540312500000000000000000000000000 : ℝ)*base76 + (6284967420325975113/1080625000000000000000000000000000 : ℝ)*base78 + (2195150243243381857/540312500000000000000000000000000 : ℝ)*base79 + (138035187090881/43225000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (16296277/2500000000000000000000 : ℝ)*base90 + (16296277/2500000000000000000000 : ℝ)*base92 + (16296277/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1572_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1572_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1572_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1572_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1572_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1572_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1572_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
