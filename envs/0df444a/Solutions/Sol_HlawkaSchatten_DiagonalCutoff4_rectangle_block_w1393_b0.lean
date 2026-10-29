-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1393_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:40:40.320935+00:00
-- url     : https://prove2.me/submissions/5a54a817-0b8d-45fe-804a-a89fb9e2f958

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
theorem support_rectangle_w1393_s0_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-889688801/5000000000 : ℝ)*x 0 + (2987589581/5000000000 : ℝ)*x 1 + (964586087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889688801/5000000000 : ℝ)^4353 ≤ (326964577533/3125000000000 : ℝ)^3329 := by
    have hnat : (889688801 : ℕ)^4353*3125000000000^3329 ≤ 326964577533^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889688801 5000000000 326964577533 3125000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2987589581/5000000000 : ℝ)^4353 ≤ (50998394647357/100000000000000 : ℝ)^3329 := by
    have hnat : (2987589581 : ℕ)^4353*100000000000000^3329 ≤ 50998394647357^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2987589581 5000000000 50998394647357 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964586087/2000000000 : ℝ)^4353 ≤ (38538738863771/100000000000000 : ℝ)^3329 := by
    have hnat : (964586087 : ℕ)^4353*100000000000000^3329 ≤ 38538738863771^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964586087 2000000000 38538738863771 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-889688801/5000000000 : ℝ), (2987589581/5000000000 : ℝ), (964586087/2000000000 : ℝ)] ![(326964577533/3125000000000 : ℝ), (50998394647357/100000000000000 : ℝ), (38538738863771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-889688801/5000000000 : ℝ)|^4353 ≤ (326964577533/3125000000000 : ℝ)^3329
        have hw : |(-889688801/5000000000 : ℝ)|=(889688801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2987589581/5000000000 : ℝ)|^4353 ≤ (50998394647357/100000000000000 : ℝ)^3329
        have hw : |(2987589581/5000000000 : ℝ)|=(2987589581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(964586087/2000000000 : ℝ)|^4353 ≤ (38538738863771/100000000000000 : ℝ)^3329
        have hw : |(964586087/2000000000 : ℝ)|=(964586087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5496110353/10000000000 : ℝ)*x 0 + (-2431921197/10000000000 : ℝ)*x 1 + (4822930553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5496110353/10000000000 : ℝ)^4353 ≤ (45718979712429/100000000000000 : ℝ)^3329 := by
    have hnat : (5496110353 : ℕ)^4353*100000000000000^3329 ≤ 45718979712429^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496110353 10000000000 45718979712429 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2431921197/10000000000 : ℝ)^4353 ≤ (7871140087419/50000000000000 : ℝ)^3329 := by
    have hnat : (2431921197 : ℕ)^4353*50000000000000^3329 ≤ 7871140087419^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431921197 10000000000 7871140087419 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4822930553/10000000000 : ℝ)^4353 ≤ (7707748019343/20000000000000 : ℝ)^3329 := by
    have hnat : (4822930553 : ℕ)^4353*20000000000000^3329 ≤ 7707748019343^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822930553 10000000000 7707748019343 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5496110353/10000000000 : ℝ), (-2431921197/10000000000 : ℝ), (4822930553/10000000000 : ℝ)] ![(45718979712429/100000000000000 : ℝ), (7871140087419/50000000000000 : ℝ), (7707748019343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5496110353/10000000000 : ℝ)|^4353 ≤ (45718979712429/100000000000000 : ℝ)^3329
        have hw : |(5496110353/10000000000 : ℝ)|=(5496110353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2431921197/10000000000 : ℝ)|^4353 ≤ (7871140087419/50000000000000 : ℝ)^3329
        have hw : |(-2431921197/10000000000 : ℝ)|=(2431921197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4822930553/10000000000 : ℝ)|^4353 ≤ (7707748019343/20000000000000 : ℝ)^3329
        have hw : |(4822930553/10000000000 : ℝ)|=(4822930553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1099222073/2000000000 : ℝ)*x 0 + (2411465261/5000000000 : ℝ)*x 1 + (-2431921219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099222073/2000000000 : ℝ)^4353 ≤ (9143795968591/20000000000000 : ℝ)^3329 := by
    have hnat : (1099222073 : ℕ)^4353*20000000000000^3329 ≤ 9143795968591^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099222073 2000000000 9143795968591 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2411465261/5000000000 : ℝ)^4353 ≤ (19269369886403/50000000000000 : ℝ)^3329 := by
    have hnat : (2411465261 : ℕ)^4353*50000000000000^3329 ≤ 19269369886403^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411465261 5000000000 19269369886403 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2431921219/10000000000 : ℝ)^4353 ≤ (7871140180527/50000000000000 : ℝ)^3329 := by
    have hnat : (2431921219 : ℕ)^4353*50000000000000^3329 ≤ 7871140180527^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431921219 10000000000 7871140180527 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099222073/2000000000 : ℝ), (2411465261/5000000000 : ℝ), (-2431921219/10000000000 : ℝ)] ![(9143795968591/20000000000000 : ℝ), (19269369886403/50000000000000 : ℝ), (7871140180527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099222073/2000000000 : ℝ)|^4353 ≤ (9143795968591/20000000000000 : ℝ)^3329
        have hw : |(1099222073/2000000000 : ℝ)|=(1099222073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2411465261/5000000000 : ℝ)|^4353 ≤ (19269369886403/50000000000000 : ℝ)^3329
        have hw : |(2411465261/5000000000 : ℝ)|=(2411465261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2431921219/10000000000 : ℝ)|^4353 ≤ (7871140180527/50000000000000 : ℝ)^3329
        have hw : |(-2431921219/10000000000 : ℝ)|=(2431921219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s0_3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042802297/2500000000 : ℝ)*x 0 + (620884491/2000000000 : ℝ)*x 1 + (5564281307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042802297/2500000000 : ℝ)^4353 ≤ (31875323287921/100000000000000 : ℝ)^3329 := by
    have hnat : (1042802297 : ℕ)^4353*100000000000000^3329 ≤ 31875323287921^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042802297 2500000000 31875323287921 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620884491/2000000000 : ℝ)^4353 ≤ (270784741909/1250000000000 : ℝ)^3329 := by
    have hnat : (620884491 : ℕ)^4353*1250000000000^3329 ≤ 270784741909^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620884491 2000000000 270784741909 1250000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5564281307/10000000000 : ℝ)^4353 ≤ (46461897351511/100000000000000 : ℝ)^3329 := by
    have hnat : (5564281307 : ℕ)^4353*100000000000000^3329 ≤ 46461897351511^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5564281307 10000000000 46461897351511 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042802297/2500000000 : ℝ), (620884491/2000000000 : ℝ), (5564281307/10000000000 : ℝ)] ![(31875323287921/100000000000000 : ℝ), (270784741909/1250000000000 : ℝ), (46461897351511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042802297/2500000000 : ℝ)|^4353 ≤ (31875323287921/100000000000000 : ℝ)^3329
        have hw : |(1042802297/2500000000 : ℝ)|=(1042802297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620884491/2000000000 : ℝ)|^4353 ≤ (270784741909/1250000000000 : ℝ)^3329
        have hw : |(620884491/2000000000 : ℝ)|=(620884491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5564281307/10000000000 : ℝ)|^4353 ≤ (46461897351511/100000000000000 : ℝ)^3329
        have hw : |(5564281307/10000000000 : ℝ)|=(5564281307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s0_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1783572973/10000000000 : ℝ)*x 0 + (1213122247/2500000000 : ℝ)*x 1 + (5944564081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1783572973/10000000000 : ℝ)^4353 ≤ (10495135456733/100000000000000 : ℝ)^3329 := by
    have hnat : (1783572973 : ℕ)^4353*100000000000000^3329 ≤ 10495135456733^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783572973 10000000000 10495135456733 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213122247/2500000000 : ℝ)^4353 ≤ (38847877395509/100000000000000 : ℝ)^3329 := by
    have hnat : (1213122247 : ℕ)^4353*100000000000000^3329 ≤ 38847877395509^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213122247 2500000000 38847877395509 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5944564081/10000000000 : ℝ)^4353 ≤ (50656987127971/100000000000000 : ℝ)^3329 := by
    have hnat : (5944564081 : ℕ)^4353*100000000000000^3329 ≤ 50656987127971^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5944564081 10000000000 50656987127971 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1783572973/10000000000 : ℝ), (1213122247/2500000000 : ℝ), (5944564081/10000000000 : ℝ)] ![(10495135456733/100000000000000 : ℝ), (38847877395509/100000000000000 : ℝ), (50656987127971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1783572973/10000000000 : ℝ)|^4353 ≤ (10495135456733/100000000000000 : ℝ)^3329
        have hw : |(-1783572973/10000000000 : ℝ)|=(1783572973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1213122247/2500000000 : ℝ)|^4353 ≤ (38847877395509/100000000000000 : ℝ)^3329
        have hw : |(1213122247/2500000000 : ℝ)|=(1213122247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5944564081/10000000000 : ℝ)|^4353 ≤ (50656987127971/100000000000000 : ℝ)^3329
        have hw : |(5944564081/10000000000 : ℝ)|=(5944564081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s0_5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259089793/500000000 : ℝ)*x 0 + (-1310287507/10000000000 : ℝ)*x 1 + (5944561913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259089793/500000000 : ℝ)^4353 ≤ (42330604865073/100000000000000 : ℝ)^3329 := by
    have hnat : (259089793 : ℕ)^4353*100000000000000^3329 ≤ 42330604865073^3329*500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259089793 500000000 42330604865073 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310287507/10000000000 : ℝ)^4353 ≤ (438277009711/6250000000000 : ℝ)^3329 := by
    have hnat : (1310287507 : ℕ)^4353*6250000000000^3329 ≤ 438277009711^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310287507 10000000000 438277009711 6250000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5944561913/10000000000 : ℝ)^4353 ≤ (12664240742597/25000000000000 : ℝ)^3329 := by
    have hnat : (5944561913 : ℕ)^4353*25000000000000^3329 ≤ 12664240742597^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5944561913 10000000000 12664240742597 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259089793/500000000 : ℝ), (-1310287507/10000000000 : ℝ), (5944561913/10000000000 : ℝ)] ![(42330604865073/100000000000000 : ℝ), (438277009711/6250000000000 : ℝ), (12664240742597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259089793/500000000 : ℝ)|^4353 ≤ (42330604865073/100000000000000 : ℝ)^3329
        have hw : |(259089793/500000000 : ℝ)|=(259089793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1310287507/10000000000 : ℝ)|^4353 ≤ (438277009711/6250000000000 : ℝ)^3329
        have hw : |(-1310287507/10000000000 : ℝ)|=(1310287507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5944561913/10000000000 : ℝ)|^4353 ≤ (12664240742597/25000000000000 : ℝ)^3329
        have hw : |(5944561913/10000000000 : ℝ)|=(5944561913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s0_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036358241/2000000000 : ℝ)*x 0 + (2972283593/5000000000 : ℝ)*x 1 + (-655143107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036358241/2000000000 : ℝ)^4353 ≤ (21165277570387/50000000000000 : ℝ)^3329 := by
    have hnat : (1036358241 : ℕ)^4353*50000000000000^3329 ≤ 21165277570387^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036358241 2000000000 21165277570387 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2972283593/5000000000 : ℝ)^4353 ≤ (25328510863179/50000000000000 : ℝ)^3329 := by
    have hnat : (2972283593 : ℕ)^4353*50000000000000^3329 ≤ 25328510863179^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2972283593 5000000000 25328510863179 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655143107/5000000000 : ℝ)^4353 ≤ (7012423106901/100000000000000 : ℝ)^3329 := by
    have hnat : (655143107 : ℕ)^4353*100000000000000^3329 ≤ 7012423106901^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655143107 5000000000 7012423106901 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036358241/2000000000 : ℝ), (2972283593/5000000000 : ℝ), (-655143107/5000000000 : ℝ)] ![(21165277570387/50000000000000 : ℝ), (25328510863179/50000000000000 : ℝ), (7012423106901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036358241/2000000000 : ℝ)|^4353 ≤ (21165277570387/50000000000000 : ℝ)^3329
        have hw : |(1036358241/2000000000 : ℝ)|=(1036358241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2972283593/5000000000 : ℝ)|^4353 ≤ (25328510863179/50000000000000 : ℝ)^3329
        have hw : |(2972283593/5000000000 : ℝ)|=(2972283593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-655143107/5000000000 : ℝ)|^4353 ≤ (7012423106901/100000000000000 : ℝ)^3329
        have hw : |(-655143107/5000000000 : ℝ)|=(655143107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180158221/10000000000 : ℝ)*x 0 + (5501180127/10000000000 : ℝ)*x 1 + (1584892083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180158221/10000000000 : ℝ)^4353 ≤ (31964774621083/100000000000000 : ℝ)^3329 := by
    have hnat : (4180158221 : ℕ)^4353*100000000000000^3329 ≤ 31964774621083^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180158221 10000000000 31964774621083 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501180127/10000000000 : ℝ)^4353 ≤ (1144353308327/2500000000000 : ℝ)^3329 := by
    have hnat : (5501180127 : ℕ)^4353*2500000000000^3329 ≤ 1144353308327^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501180127 10000000000 1144353308327 2500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584892083/5000000000 : ℝ)^4353 ≤ (22261093038731/100000000000000 : ℝ)^3329 := by
    have hnat : (1584892083 : ℕ)^4353*100000000000000^3329 ≤ 22261093038731^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584892083 5000000000 22261093038731 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180158221/10000000000 : ℝ), (5501180127/10000000000 : ℝ), (1584892083/5000000000 : ℝ)] ![(31964774621083/100000000000000 : ℝ), (1144353308327/2500000000000 : ℝ), (22261093038731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180158221/10000000000 : ℝ)|^4353 ≤ (31964774621083/100000000000000 : ℝ)^3329
        have hw : |(4180158221/10000000000 : ℝ)|=(4180158221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501180127/10000000000 : ℝ)|^4353 ≤ (1144353308327/2500000000000 : ℝ)^3329
        have hw : |(5501180127/10000000000 : ℝ)|=(5501180127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584892083/5000000000 : ℝ)|^4353 ≤ (22261093038731/100000000000000 : ℝ)^3329
        have hw : |(1584892083/5000000000 : ℝ)|=(1584892083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1393_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (179/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26509/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (17/4 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^17 ≤ (0 : ℝ)^4 := by
      have hnat : (0 : ℕ)^17*1^4 ≤ 0^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (17/4 : ℝ) ≤ (2035893065643649703/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^17 ≤ (2035893065643649703/100000000000000000000 : ℝ)^4 := by
      have hnat : (2 : ℕ)^17*100000000000000000000^4 ≤ 2035893065643649703^4*5^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2035893065643649703 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2035893065643649703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (1 : ℝ)^4 ≤ (1 : ℝ)^17 := by
      have hnat : (1 : ℕ)^4*1^17 ≤ 1^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner10 : (102035893065643649703/100000000000000000000 : ℝ) ≤ (2511883719011851/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (102035893065643649703/100000000000000000000 : ℝ)^4 ≤ (2511883719011851/2500000000000000 : ℝ)^17 := by
      have hnat : (102035893065643649703 : ℕ)^4*2500000000000000^17 ≤ 2511883719011851^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102035893065643649703 100000000000000000000 2511883719011851 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511883719011851/2500000000000000 : ℝ)) (X := (102035893065643649703/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner11 : (52035893065643649703/50000000000000000000 : ℝ) ≤ (1261883719011851/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (52035893065643649703/50000000000000000000 : ℝ)^4 ≤ (1261883719011851/1250000000000000 : ℝ)^17 := by
      have hnat : (52035893065643649703 : ℕ)^4*1250000000000000^17 ≤ 1261883719011851^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52035893065643649703 50000000000000000000 1261883719011851 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261883719011851/1250000000000000 : ℝ)) (X := (52035893065643649703/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11883719011851/1000000000000000 : ℝ)*(0 : ℝ))^(17/4 : ℝ) := by
    rw [show (1 : ℝ)+2*(11883719011851/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2035893065643649703/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11883719011851/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(17/4 : ℝ) := by
    rw [show (1 : ℝ)+(11883719011851/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511883719011851/2500000000000000 : ℝ) by norm_num, show 1+(2035893065643649703/100000000000000000000 : ℝ)+(0 : ℝ)=(102035893065643649703/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2035893065643649703/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11883719011851/1000000000000000 : ℝ)*(2/5 : ℝ))^(17/4 : ℝ) := by
    rw [show (1 : ℝ)+2*(11883719011851/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261883719011851/1250000000000000 : ℝ) by norm_num, show 1+2*(2035893065643649703/100000000000000000000 : ℝ)=(52035893065643649703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11883719011851/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11883719011851/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11883719011851/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11883719011851/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11883719011851/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11883719011851/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-889688801/5000000000 : ℝ)*X 0 0+(2987589581/5000000000 : ℝ)*X 0 1+(964586087/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5496110353/10000000000 : ℝ)*X 1 0+(-2431921197/10000000000 : ℝ)*X 1 1+(4822930553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1099222073/2000000000 : ℝ)*X 2 0+(2411465261/5000000000 : ℝ)*X 2 1+(-2431921219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1042802297/2500000000 : ℝ)*X 0 0+(620884491/2000000000 : ℝ)*X 0 1+(5564281307/10000000000 : ℝ)*X 0 2+(1042802297/2500000000 : ℝ)*X 1 0+(620884491/2000000000 : ℝ)*X 1 1+(5564281307/10000000000 : ℝ)*X 1 2+(1042802297/2500000000 : ℝ)*X 2 0+(620884491/2000000000 : ℝ)*X 2 1+(5564281307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1783572973/10000000000 : ℝ)*X 0 0+(1213122247/2500000000 : ℝ)*X 0 1+(5944564081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((259089793/500000000 : ℝ)*X 1 0+(-1310287507/10000000000 : ℝ)*X 1 1+(5944561913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1036358241/2000000000 : ℝ)*X 2 0+(2972283593/5000000000 : ℝ)*X 2 1+(-655143107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180158221/10000000000 : ℝ)*X 0 0+(5501180127/10000000000 : ℝ)*X 0 1+(1584892083/5000000000 : ℝ)*X 0 2+(4180158221/10000000000 : ℝ)*X 1 0+(5501180127/10000000000 : ℝ)*X 1 1+(1584892083/5000000000 : ℝ)*X 1 2+(4180158221/10000000000 : ℝ)*X 2 0+(5501180127/10000000000 : ℝ)*X 2 1+(1584892083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12920816380934172035979/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24461309/50000000000000 : ℝ)*(base1) + (301800987/20000000000000 : ℝ)*(base19) + (94431239/6250000000000 : ℝ)*(base23) + (189315307/100000000000000 : ℝ)*(upper3) + (1437907/781250000000 : ℝ)*(upper5) + (25488211682443/4000000000000 : ℝ)*(major0) + (25488211682443/4000000000000 : ℝ)*(major1) + (25488211682443/4000000000000 : ℝ)*(major2) + (433936547365193/50000000000000 : ℝ)*(sp0) + (10848458686631/1250000000000 : ℝ)*(sp1) + (867876693035591/100000000000000 : ℝ)*(sp2) + (406529681876687/100000000000000 : ℝ)*(sp3) + (2579063823/50000000000000 : ℝ)*(sp4) + (1217020243/50000000000000 : ℝ)*(sp7) + (40653216483979/10000000000000 : ℝ)*(f.failure) + (173575640787083/20000000000000 : ℝ)*(f.sum) + (5218253632007/2000000000000000000000000000 : ℝ)*base66 + (7005337283993/4000000000000000000000000000 : ℝ)*base67 + (8792902347993/4000000000000000000000000000 : ℝ)*base69 + (11119414376007/4000000000000000000000000000 : ℝ)*base72 + (2971921862007/2000000000000000000000000000 : ℝ)*base74 + (14485394468007/4000000000000000000000000000 : ℝ)*base76 + (16182379476007/4000000000000000000000000000 : ℝ)*base78 + (1735618395993/4000000000000000000000000000 : ℝ)*base79 + (1034507319993/2000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2747007/1000000000000000000000 : ℝ)*base90 + (2747007/1000000000000000000000 : ℝ)*base92 + (2747007/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112802345429842720485801/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1777741443/100000000000000 : ℝ)*(base19) + (874922651/50000000000000 : ℝ)*(base23) + (82075673/20000000000000 : ℝ)*(base39) + (24345481/12500000000000 : ℝ)*(upper2) + (362037137/100000000000000 : ℝ)*(upper5) + (336152970809137/50000000000000 : ℝ)*(major0) + (336152970809137/50000000000000 : ℝ)*(major1) + (67230553123991/10000000000000 : ℝ)*(major2) + (4657782709/100000000000000 : ℝ)*(sp1) + (38689701/781250000000 : ℝ)*(sp2) + (457842528918667/50000000000000 : ℝ)*(sp4) + (915678622313181/100000000000000 : ℝ)*(sp5) + (228919691522167/25000000000000 : ℝ)*(sp6) + (428926114214591/100000000000000 : ℝ)*(sp7) + (428926114214591/100000000000000 : ℝ)*(f.failure) + (457842734107849/50000000000000 : ℝ)*(f.sum) + (12333534429823/12500000000000000000000000000 : ℝ)*base65 + (15041509072659/10000000000000000000000000000 : ℝ)*base68 + (69839254082587/50000000000000000000000000000 : ℝ)*base69 + (16334405937341/10000000000000000000000000000 : ℝ)*base71 + (13512384579823/12500000000000000000000000000 : ℝ)*base73 + (521615090282587/50000000000000000000000000000 : ℝ)*base75 + (28416351467413/50000000000000000000000000000 : ℝ)*base78 + (80798396032587/50000000000000000000000000000 : ℝ)*base79 + (12928644032587/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (10936803/10000000000000000000000 : ℝ)*base90 + (10936803/10000000000000000000000 : ℝ)*base92 + (110936803/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1393_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (179/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26509/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1393_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1393_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-391371831/2000000000 : ℝ)*x 0 + (702500267/1250000000 : ℝ)*x 1 + (1012876997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391371831/2000000000 : ℝ)^4353 ≤ (11847954475723/100000000000000 : ℝ)^3329 := by
    have hnat : (391371831 : ℕ)^4353*100000000000000^3329 ≤ 11847954475723^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391371831 2000000000 11847954475723 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702500267/1250000000 : ℝ)^4353 ≤ (11767804934241/25000000000000 : ℝ)^3329 := by
    have hnat : (702500267 : ℕ)^4353*25000000000000^3329 ≤ 11767804934241^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702500267 1250000000 11767804934241 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012876997/2000000000 : ℝ)^4353 ≤ (1027020644183/2500000000000 : ℝ)^3329 := by
    have hnat : (1012876997 : ℕ)^4353*2500000000000^3329 ≤ 1027020644183^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012876997 2000000000 1027020644183 2500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391371831/2000000000 : ℝ), (702500267/1250000000 : ℝ), (1012876997/2000000000 : ℝ)] ![(11847954475723/100000000000000 : ℝ), (11767804934241/25000000000000 : ℝ), (1027020644183/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391371831/2000000000 : ℝ)|^4353 ≤ (11847954475723/100000000000000 : ℝ)^3329
        have hw : |(-391371831/2000000000 : ℝ)|=(391371831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(702500267/1250000000 : ℝ)|^4353 ≤ (11767804934241/25000000000000 : ℝ)^3329
        have hw : |(702500267/1250000000 : ℝ)|=(702500267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1012876997/2000000000 : ℝ)|^4353 ≤ (1027020644183/2500000000000 : ℝ)^3329
        have hw : |(1012876997/2000000000 : ℝ)|=(1012876997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400455359/10000000000 : ℝ)*x 0 + (-450420289/2000000000 : ℝ)*x 1 + (316524149/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400455359/10000000000 : ℝ)^4353 ≤ (44681320295401/100000000000000 : ℝ)^3329 := by
    have hnat : (5400455359 : ℕ)^4353*100000000000000^3329 ≤ 44681320295401^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400455359 10000000000 44681320295401 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450420289/2000000000 : ℝ)^4353 ≤ (2847567816681/20000000000000 : ℝ)^3329 := by
    have hnat : (450420289 : ℕ)^4353*20000000000000^3329 ≤ 2847567816681^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450420289 2000000000 2847567816681 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316524149/625000000 : ℝ)^4353 ≤ (8216168121267/20000000000000 : ℝ)^3329 := by
    have hnat : (316524149 : ℕ)^4353*20000000000000^3329 ≤ 8216168121267^3329*625000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316524149 625000000 8216168121267 20000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400455359/10000000000 : ℝ), (-450420289/2000000000 : ℝ), (316524149/625000000 : ℝ)] ![(44681320295401/100000000000000 : ℝ), (2847567816681/20000000000000 : ℝ), (8216168121267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400455359/10000000000 : ℝ)|^4353 ≤ (44681320295401/100000000000000 : ℝ)^3329
        have hw : |(5400455359/10000000000 : ℝ)|=(5400455359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450420289/2000000000 : ℝ)|^4353 ≤ (2847567816681/20000000000000 : ℝ)^3329
        have hw : |(-450420289/2000000000 : ℝ)|=(450420289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316524149/625000000 : ℝ)|^4353 ≤ (8216168121267/20000000000000 : ℝ)^3329
        have hw : |(316524149/625000000 : ℝ)|=(316524149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400456247/10000000000 : ℝ)*x 0 + (316524073/625000000 : ℝ)*x 1 + (-563025461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400456247/10000000000 : ℝ)^4353 ≤ (22340664951153/50000000000000 : ℝ)^3329 := by
    have hnat : (5400456247 : ℕ)^4353*50000000000000^3329 ≤ 22340664951153^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400456247 10000000000 22340664951153 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316524073/625000000 : ℝ)^4353 ≤ (20540413854189/50000000000000 : ℝ)^3329 := by
    have hnat : (316524073 : ℕ)^4353*50000000000000^3329 ≤ 20540413854189^3329*625000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316524073 625000000 20540413854189 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563025461/2500000000 : ℝ)^4353 ≤ (1423784238181/10000000000000 : ℝ)^3329 := by
    have hnat : (563025461 : ℕ)^4353*10000000000000^3329 ≤ 1423784238181^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563025461 2500000000 1423784238181 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400456247/10000000000 : ℝ), (316524073/625000000 : ℝ), (-563025461/2500000000 : ℝ)] ![(22340664951153/50000000000000 : ℝ), (20540413854189/50000000000000 : ℝ), (1423784238181/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400456247/10000000000 : ℝ)|^4353 ≤ (22340664951153/50000000000000 : ℝ)^3329
        have hw : |(5400456247/10000000000 : ℝ)|=(5400456247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(316524073/625000000 : ℝ)|^4353 ≤ (20540413854189/50000000000000 : ℝ)^3329
        have hw : |(316524073/625000000 : ℝ)|=(316524073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563025461/2500000000 : ℝ)|^4353 ≤ (1423784238181/10000000000000 : ℝ)^3329
        have hw : |(-563025461/2500000000 : ℝ)|=(563025461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s1_3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283157919/10000000000 : ℝ)*x 0 + (465913309/1250000000 : ℝ)*x 1 + (2456726329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283157919/10000000000 : ℝ)^4353 ≤ (4124817872569/12500000000000 : ℝ)^3329 := by
    have hnat : (4283157919 : ℕ)^4353*12500000000000^3329 ≤ 4124817872569^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283157919 10000000000 4124817872569 12500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465913309/1250000000 : ℝ)^4353 ≤ (13757080958793/50000000000000 : ℝ)^3329 := by
    have hnat : (465913309 : ℕ)^4353*50000000000000^3329 ≤ 13757080958793^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465913309 1250000000 13757080958793 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2456726329/5000000000 : ℝ)^4353 ≤ (77123623223/195312500000 : ℝ)^3329 := by
    have hnat : (2456726329 : ℕ)^4353*195312500000^3329 ≤ 77123623223^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2456726329 5000000000 77123623223 195312500000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283157919/10000000000 : ℝ), (465913309/1250000000 : ℝ), (2456726329/5000000000 : ℝ)] ![(4124817872569/12500000000000 : ℝ), (13757080958793/50000000000000 : ℝ), (77123623223/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283157919/10000000000 : ℝ)|^4353 ≤ (4124817872569/12500000000000 : ℝ)^3329
        have hw : |(4283157919/10000000000 : ℝ)|=(4283157919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(465913309/1250000000 : ℝ)|^4353 ≤ (13757080958793/50000000000000 : ℝ)^3329
        have hw : |(465913309/1250000000 : ℝ)|=(465913309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2456726329/5000000000 : ℝ)|^4353 ≤ (77123623223/195312500000 : ℝ)^3329
        have hw : |(2456726329/5000000000 : ℝ)|=(2456726329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s1_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-978654849/5000000000 : ℝ)*x 0 + (5071087071/10000000000 : ℝ)*x 1 + (2806591483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978654849/5000000000 : ℝ)^4353 ≤ (11851521534819/100000000000000 : ℝ)^3329 := by
    have hnat : (978654849 : ℕ)^4353*100000000000000^3329 ≤ 11851521534819^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978654849 5000000000 11851521534819 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5071087071/10000000000 : ℝ)^4353 ≤ (1646077135983/4000000000000 : ℝ)^3329 := by
    have hnat : (5071087071 : ℕ)^4353*4000000000000^3329 ≤ 1646077135983^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071087071 10000000000 1646077135983 4000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2806591483/5000000000 : ℝ)^4353 ≤ (23498275029017/50000000000000 : ℝ)^3329 := by
    have hnat : (2806591483 : ℕ)^4353*50000000000000^3329 ≤ 23498275029017^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806591483 5000000000 23498275029017 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978654849/5000000000 : ℝ), (5071087071/10000000000 : ℝ), (2806591483/5000000000 : ℝ)] ![(11851521534819/100000000000000 : ℝ), (1646077135983/4000000000000 : ℝ), (23498275029017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978654849/5000000000 : ℝ)|^4353 ≤ (11851521534819/100000000000000 : ℝ)^3329
        have hw : |(-978654849/5000000000 : ℝ)|=(978654849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5071087071/10000000000 : ℝ)|^4353 ≤ (1646077135983/4000000000000 : ℝ)^3329
        have hw : |(5071087071/10000000000 : ℝ)|=(5071087071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2806591483/5000000000 : ℝ)|^4353 ≤ (23498275029017/50000000000000 : ℝ)^3329
        have hw : |(2806591483/5000000000 : ℝ)|=(2806591483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s1_5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627842443/5000000000 : ℝ)*x 0 + (-1703304733/10000000000 : ℝ)*x 1 + (1403295743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627842443/5000000000 : ℝ)^4353 ≤ (5390200789897/12500000000000 : ℝ)^3329 := by
    have hnat : (2627842443 : ℕ)^4353*12500000000000^3329 ≤ 5390200789897^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627842443 5000000000 5390200789897 12500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1703304733/10000000000 : ℝ)^4353 ≤ (2470460885121/25000000000000 : ℝ)^3329 := by
    have hnat : (1703304733 : ℕ)^4353*25000000000000^3329 ≤ 2470460885121^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703304733 10000000000 2470460885121 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403295743/2500000000 : ℝ)^4353 ≤ (46996550123721/100000000000000 : ℝ)^3329 := by
    have hnat : (1403295743 : ℕ)^4353*100000000000000^3329 ≤ 46996550123721^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403295743 2500000000 46996550123721 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627842443/5000000000 : ℝ), (-1703304733/10000000000 : ℝ), (1403295743/2500000000 : ℝ)] ![(5390200789897/12500000000000 : ℝ), (2470460885121/25000000000000 : ℝ), (46996550123721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627842443/5000000000 : ℝ)|^4353 ≤ (5390200789897/12500000000000 : ℝ)^3329
        have hw : |(2627842443/5000000000 : ℝ)|=(2627842443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1703304733/10000000000 : ℝ)|^4353 ≤ (2470460885121/25000000000000 : ℝ)^3329
        have hw : |(-1703304733/10000000000 : ℝ)|=(1703304733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1403295743/2500000000 : ℝ)|^4353 ≤ (46996550123721/100000000000000 : ℝ)^3329
        have hw : |(1403295743/2500000000 : ℝ)|=(1403295743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051137067/2000000000 : ℝ)*x 0 + (5613183357/10000000000 : ℝ)*x 1 + (-212912943/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051137067/2000000000 : ℝ)^4353 ≤ (43121611136289/100000000000000 : ℝ)^3329 := by
    have hnat : (1051137067 : ℕ)^4353*100000000000000^3329 ≤ 43121611136289^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051137067 2000000000 43121611136289 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5613183357/10000000000 : ℝ)^4353 ≤ (46996554338671/100000000000000 : ℝ)^3329 := by
    have hnat : (5613183357 : ℕ)^4353*100000000000000^3329 ≤ 46996554338671^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5613183357 10000000000 46996554338671 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212912943/1250000000 : ℝ)^4353 ≤ (2470458630143/25000000000000 : ℝ)^3329 := by
    have hnat : (212912943 : ℕ)^4353*25000000000000^3329 ≤ 2470458630143^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212912943 1250000000 2470458630143 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051137067/2000000000 : ℝ), (5613183357/10000000000 : ℝ), (-212912943/1250000000 : ℝ)] ![(43121611136289/100000000000000 : ℝ), (46996554338671/100000000000000 : ℝ), (2470458630143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051137067/2000000000 : ℝ)|^4353 ≤ (43121611136289/100000000000000 : ℝ)^3329
        have hw : |(1051137067/2000000000 : ℝ)|=(1051137067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5613183357/10000000000 : ℝ)|^4353 ≤ (46996554338671/100000000000000 : ℝ)^3329
        have hw : |(5613183357/10000000000 : ℝ)|=(5613183357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212912943/1250000000 : ℝ)|^4353 ≤ (2470458630143/25000000000000 : ℝ)^3329
        have hw : |(-212912943/1250000000 : ℝ)|=(212912943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284121293/10000000000 : ℝ)*x 0 + (4899145191/10000000000 : ℝ)*x 1 + (1870930923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284121293/10000000000 : ℝ)^4353 ≤ (8252062106613/25000000000000 : ℝ)^3329 := by
    have hnat : (4284121293 : ℕ)^4353*25000000000000^3329 ≤ 8252062106613^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284121293 10000000000 8252062106613 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4899145191/10000000000 : ℝ)^4353 ≤ (2458563175503/6250000000000 : ℝ)^3329 := by
    have hnat : (4899145191 : ℕ)^4353*6250000000000^3329 ≤ 2458563175503^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899145191 10000000000 2458563175503 6250000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870930923/5000000000 : ℝ)^4353 ≤ (27654740755939/100000000000000 : ℝ)^3329 := by
    have hnat : (1870930923 : ℕ)^4353*100000000000000^3329 ≤ 27654740755939^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870930923 5000000000 27654740755939 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284121293/10000000000 : ℝ), (4899145191/10000000000 : ℝ), (1870930923/5000000000 : ℝ)] ![(8252062106613/25000000000000 : ℝ), (2458563175503/6250000000000 : ℝ), (27654740755939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284121293/10000000000 : ℝ)|^4353 ≤ (8252062106613/25000000000000 : ℝ)^3329
        have hw : |(4284121293/10000000000 : ℝ)|=(4284121293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4899145191/10000000000 : ℝ)|^4353 ≤ (2458563175503/6250000000000 : ℝ)^3329
        have hw : |(4899145191/10000000000 : ℝ)|=(4899145191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1870930923/5000000000 : ℝ)|^4353 ≤ (27654740755939/100000000000000 : ℝ)^3329
        have hw : |(1870930923/5000000000 : ℝ)|=(1870930923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1393_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26509/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (179/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (7347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4773/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26509/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (179/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26509/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (179/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26509/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (179/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26509/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (179/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26509/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (179/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26509/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (179/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (179/10000 : ℝ) ^ (17/4 : ℝ) ≤ (751026700523/20000000000000000000 : ℝ) := by
    have hpowers : (179/10000 : ℝ)^17 ≤ (751026700523/20000000000000000000 : ℝ)^4 := by
      have hnat : (179 : ℕ)^17*20000000000000000000^4 ≤ 751026700523^4*10000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        179 10000 751026700523 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (179/10000 : ℝ)) (X := (751026700523/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hpowhi : (26509/100000 : ℝ) ^ (17/4 : ℝ) ≤ (354341253211438749/100000000000000000000 : ℝ) := by
    have hpowers : (26509/100000 : ℝ)^17 ≤ (354341253211438749/100000000000000000000 : ℝ)^4 := by
      have hnat : (26509 : ℕ)^17*100000000000000000000^4 ≤ 354341253211438749^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26509 100000 354341253211438749 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26509/100000 : ℝ)) (X := (354341253211438749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000751026700523/10000000000000000000 : ℝ) ≤ (62500001104451/62500000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (10000000751026700523/10000000000000000000 : ℝ)^4 ≤ (62500001104451/62500000000000 : ℝ)^17 := by
      have hnat : (10000000751026700523 : ℕ)^4*62500000000000^17 ≤ 62500001104451^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000751026700523 10000000000000000000 62500001104451 62500000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500001104451/62500000000000 : ℝ)) (X := (10000000751026700523/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner10 : (25088586252086235341/25000000000000000000 : ℝ) ≤ (10008326257005981/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (25088586252086235341/25000000000000000000 : ℝ)^4 ≤ (10008326257005981/10000000000000000 : ℝ)^17 := by
      have hnat : (25088586252086235341 : ℕ)^4*10000000000000000^17 ≤ 10008326257005981^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25088586252086235341 25000000000000000000 10008326257005981 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008326257005981/10000000000000000 : ℝ)) (X := (25088586252086235341/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner11 : (50354341253211438749/50000000000000000000 : ℝ) ≤ (5008326168649901/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50354341253211438749/50000000000000000000 : ℝ)^4 ≤ (5008326168649901/5000000000000000 : ℝ)^17 := by
      have hnat : (50354341253211438749 : ℕ)^4*5000000000000000^17 ≤ 5008326168649901^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50354341253211438749 50000000000000000000 5008326168649901 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008326168649901/5000000000000000 : ℝ)) (X := (50354341253211438749/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(751026700523/20000000000000000000 : ℝ) ≤ ((12358009850034800193/12359500000000000000 : ℝ)+2*(8326080293821/2471900000000000 : ℝ)*(179/10000 : ℝ))^(17/4 : ℝ) := by
    rw [show (12358009850034800193/12359500000000000000 : ℝ)+2*(8326080293821/2471900000000000 : ℝ)*(179/10000 : ℝ)=(62500001104451/62500000000000 : ℝ) by norm_num, show 1+2*(751026700523/20000000000000000000 : ℝ)=(10000000751026700523/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(354341253211438749/100000000000000000000 : ℝ)+(751026700523/20000000000000000000 : ℝ) ≤ ((12358009850034800193/12359500000000000000 : ℝ)+(8326080293821/2471900000000000 : ℝ)*((26509/100000 : ℝ)+(179/10000 : ℝ)))^(17/4 : ℝ) := by
    rw [show (12358009850034800193/12359500000000000000 : ℝ)+(8326080293821/2471900000000000 : ℝ)*((26509/100000 : ℝ)+(179/10000 : ℝ))=(10008326257005981/10000000000000000 : ℝ) by norm_num, show 1+(354341253211438749/100000000000000000000 : ℝ)+(751026700523/20000000000000000000 : ℝ)=(25088586252086235341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(354341253211438749/100000000000000000000 : ℝ) ≤ ((12358009850034800193/12359500000000000000 : ℝ)+2*(8326080293821/2471900000000000 : ℝ)*(26509/100000 : ℝ))^(17/4 : ℝ) := by
    rw [show (12358009850034800193/12359500000000000000 : ℝ)+2*(8326080293821/2471900000000000 : ℝ)*(26509/100000 : ℝ)=(5008326168649901/5000000000000000 : ℝ) by norm_num, show 1+2*(354341253211438749/100000000000000000000 : ℝ)=(50354341253211438749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12358009850034800193/12359500000000000000 : ℝ)*(X 1 0+X 2 0)+(8326080293821/2471900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (179/10000 : ℝ)) (hi := (26509/100000 : ℝ)) (c := (12358009850034800193/12359500000000000000 : ℝ)) (alpha := (8326080293821/2471900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12358009850034800193/12359500000000000000 : ℝ)*(X 0 1+X 2 1)+(8326080293821/2471900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (179/10000 : ℝ)) (hi := (26509/100000 : ℝ)) (c := (12358009850034800193/12359500000000000000 : ℝ)) (alpha := (8326080293821/2471900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12358009850034800193/12359500000000000000 : ℝ)*(X 0 2+X 1 2)+(8326080293821/2471900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (179/10000 : ℝ)) (hi := (26509/100000 : ℝ)) (c := (12358009850034800193/12359500000000000000 : ℝ)) (alpha := (8326080293821/2471900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-391371831/2000000000 : ℝ)*X 0 0+(702500267/1250000000 : ℝ)*X 0 1+(1012876997/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5400455359/10000000000 : ℝ)*X 1 0+(-450420289/2000000000 : ℝ)*X 1 1+(316524149/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5400456247/10000000000 : ℝ)*X 2 0+(316524073/625000000 : ℝ)*X 2 1+(-563025461/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283157919/10000000000 : ℝ)*X 0 0+(465913309/1250000000 : ℝ)*X 0 1+(2456726329/5000000000 : ℝ)*X 0 2+(4283157919/10000000000 : ℝ)*X 1 0+(465913309/1250000000 : ℝ)*X 1 1+(2456726329/5000000000 : ℝ)*X 1 2+(4283157919/10000000000 : ℝ)*X 2 0+(465913309/1250000000 : ℝ)*X 2 1+(2456726329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-978654849/5000000000 : ℝ)*X 0 0+(5071087071/10000000000 : ℝ)*X 0 1+(2806591483/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627842443/5000000000 : ℝ)*X 1 0+(-1703304733/10000000000 : ℝ)*X 1 1+(1403295743/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051137067/2000000000 : ℝ)*X 2 0+(5613183357/10000000000 : ℝ)*X 2 1+(-212912943/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4284121293/10000000000 : ℝ)*X 0 0+(4899145191/10000000000 : ℝ)*X 0 1+(1870930923/5000000000 : ℝ)*X 0 2+(4284121293/10000000000 : ℝ)*X 1 0+(4899145191/10000000000 : ℝ)*X 1 1+(1870930923/5000000000 : ℝ)*X 1 2+(4284121293/10000000000 : ℝ)*X 2 0+(4899145191/10000000000 : ℝ)*X 2 1+(1870930923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (733374388064370901735260123/77246875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20969707/100000000000000 : ℝ)*(base1) + (1710285923/100000000000000 : ℝ)*(base19) + (1003116481/50000000000000 : ℝ)*(base23) + (233052603/100000000000000 : ℝ)*(upper3) + (126979481/100000000000000 : ℝ)*(upper5) + (330363812447837/25000000000000 : ℝ)*(major0) + (330363812447837/25000000000000 : ℝ)*(major1) + (330363812447837/25000000000000 : ℝ)*(major2) + (359963240691591/20000000000000 : ℝ)*(sp0) + (359966000337591/20000000000000 : ℝ)*(sp1) + (449957426435229/25000000000000 : ℝ)*(sp2) + (421535961222547/50000000000000 : ℝ)*(sp3) + (1552948563/10000000000000 : ℝ)*(sp4) + (3263865279/50000000000000 : ℝ)*(sp7) + (421539235572679/50000000000000 : ℝ)*(f.failure) + (899915855986939/50000000000000 : ℝ)*(f.sum) + (269884574337717/123595000000000000000000000000 : ℝ)*base66 + (1008864487241132459/308987500000000000000000000000000 : ℝ)*base68 + (2835122010791894959/308987500000000000000000000000000 : ℝ)*base70 + (1027958422022519959/308987500000000000000000000000000 : ℝ)*base72 + (288707704255037/123595000000000000000000000000 : ℝ)*base74 + (1253174131721082459/308987500000000000000000000000000 : ℝ)*base76 + (2866496279267932459/308987500000000000000000000000000 : ℝ)*base78 + (788932229510342541/308987500000000000000000000000000 : ℝ)*base79 + (140348864298203/30898750000000000000000000000 : ℝ)*base82 + (6115893/5000000000000000000000 : ℝ)*base89 + (6115893/5000000000000000000000 : ℝ)*base91 + (6115893/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (621913720823174660782774233/123595000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92842543/50000000000000 : ℝ)*(base1) + (338788521/25000000000000 : ℝ)*(base19) + (401947149/25000000000000 : ℝ)*(base23) + (123630839/100000000000000 : ℝ)*(upper3) + (212771331/100000000000000 : ℝ)*(upper5) + (270878650562191/20000000000000 : ℝ)*(major0) + (270878650562191/20000000000000 : ℝ)*(major1) + (270878650562191/20000000000000 : ℝ)*(major2) + (1340128021/20000000000000 : ℝ)*(sp1) + (1268862881/12500000000000 : ℝ)*(sp2) + (461173463804719/25000000000000 : ℝ)*(sp4) + (922342806869801/50000000000000 : ℝ)*(sp5) + (922340955421073/50000000000000 : ℝ)*(sp6) + (864092482674091/100000000000000 : ℝ)*(sp7) + (108011583544897/12500000000000 : ℝ)*(f.failure) + (1844693669533791/100000000000000 : ℝ)*(f.sum) + (12743224966387/12359500000000000000000000000 : ℝ)*base66 + (476867859165727863/247190000000000000000000000000000 : ℝ)*base67 + (430890611861977863/247190000000000000000000000000000 : ℝ)*base69 + (431249154035657863/247190000000000000000000000000000 : ℝ)*base71 + (124518134520599/24719000000000000000000000000 : ℝ)*base74 + (413606778568857863/247190000000000000000000000000000 : ℝ)*base75 + (790554230459847863/247190000000000000000000000000000 : ℝ)*base77 + (2474211510877627863/247190000000000000000000000000000 : ℝ)*base79 + (81553735588139/24719000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (12376701/1250000000000000000000 : ℝ)*base90 + (12376701/1250000000000000000000 : ℝ)*base92 + (12376701/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1393_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26509/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (179/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4773/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1393_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1393_s2_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1992767409/10000000000 : ℝ)*x 0 + (109331707/200000000 : ℝ)*x 1 + (649341789/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1992767409/10000000000 : ℝ)^4353 ≤ (6066518888947/50000000000000 : ℝ)^3329 := by
    have hnat : (1992767409 : ℕ)^4353*50000000000000^3329 ≤ 6066518888947^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992767409 10000000000 6066518888947 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109331707/200000000 : ℝ)^4353 ≤ (45398096870739/100000000000000 : ℝ)^3329 := by
    have hnat : (109331707 : ℕ)^4353*100000000000000^3329 ≤ 45398096870739^3329*200000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109331707 200000000 45398096870739 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649341789/1250000000 : ℝ)^4353 ≤ (21234432665633/50000000000000 : ℝ)^3329 := by
    have hnat : (649341789 : ℕ)^4353*50000000000000^3329 ≤ 21234432665633^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649341789 1250000000 21234432665633 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1992767409/10000000000 : ℝ), (109331707/200000000 : ℝ), (649341789/1250000000 : ℝ)] ![(6066518888947/50000000000000 : ℝ), (45398096870739/100000000000000 : ℝ), (21234432665633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1992767409/10000000000 : ℝ)|^4353 ≤ (6066518888947/50000000000000 : ℝ)^3329
        have hw : |(-1992767409/10000000000 : ℝ)|=(1992767409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109331707/200000000 : ℝ)|^4353 ≤ (45398096870739/100000000000000 : ℝ)^3329
        have hw : |(109331707/200000000 : ℝ)|=(109331707/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649341789/1250000000 : ℝ)|^4353 ≤ (21234432665633/50000000000000 : ℝ)^3329
        have hw : |(649341789/1250000000 : ℝ)|=(649341789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s2_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670309107/1250000000 : ℝ)*x 0 + (-1066433119/5000000000 : ℝ)*x 1 + (5194734269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670309107/1250000000 : ℝ)^4353 ≤ (44270848547251/100000000000000 : ℝ)^3329 := by
    have hnat : (670309107 : ℕ)^4353*100000000000000^3329 ≤ 44270848547251^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670309107 1250000000 44270848547251 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066433119/5000000000 : ℝ)^4353 ≤ (265205731361/2000000000000 : ℝ)^3329 := by
    have hnat : (1066433119 : ℕ)^4353*2000000000000^3329 ≤ 265205731361^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066433119 5000000000 265205731361 2000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194734269/10000000000 : ℝ)^4353 ≤ (42468864871591/100000000000000 : ℝ)^3329 := by
    have hnat : (5194734269 : ℕ)^4353*100000000000000^3329 ≤ 42468864871591^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194734269 10000000000 42468864871591 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670309107/1250000000 : ℝ), (-1066433119/5000000000 : ℝ), (5194734269/10000000000 : ℝ)] ![(44270848547251/100000000000000 : ℝ), (265205731361/2000000000000 : ℝ), (42468864871591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670309107/1250000000 : ℝ)|^4353 ≤ (44270848547251/100000000000000 : ℝ)^3329
        have hw : |(670309107/1250000000 : ℝ)|=(670309107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066433119/5000000000 : ℝ)|^4353 ≤ (265205731361/2000000000000 : ℝ)^3329
        have hw : |(-1066433119/5000000000 : ℝ)|=(1066433119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194734269/10000000000 : ℝ)|^4353 ≤ (42468864871591/100000000000000 : ℝ)^3329
        have hw : |(5194734269/10000000000 : ℝ)|=(5194734269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s2_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362472687/10000000000 : ℝ)*x 0 + (2597367227/5000000000 : ℝ)*x 1 + (-2132866219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362472687/10000000000 : ℝ)^4353 ≤ (354166773783/800000000000 : ℝ)^3329 := by
    have hnat : (5362472687 : ℕ)^4353*800000000000^3329 ≤ 354166773783^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362472687 10000000000 354166773783 800000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597367227/5000000000 : ℝ)^4353 ≤ (21234433424631/50000000000000 : ℝ)^3329 := by
    have hnat : (2597367227 : ℕ)^4353*50000000000000^3329 ≤ 21234433424631^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597367227 5000000000 21234433424631 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132866219/10000000000 : ℝ)^4353 ≤ (1326028641359/10000000000000 : ℝ)^3329 := by
    have hnat : (2132866219 : ℕ)^4353*10000000000000^3329 ≤ 1326028641359^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132866219 10000000000 1326028641359 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362472687/10000000000 : ℝ), (2597367227/5000000000 : ℝ), (-2132866219/10000000000 : ℝ)] ![(354166773783/800000000000 : ℝ), (21234433424631/50000000000000 : ℝ), (1326028641359/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362472687/10000000000 : ℝ)|^4353 ≤ (354166773783/800000000000 : ℝ)^3329
        have hw : |(5362472687/10000000000 : ℝ)|=(5362472687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597367227/5000000000 : ℝ)|^4353 ≤ (21234433424631/50000000000000 : ℝ)^3329
        have hw : |(2597367227/5000000000 : ℝ)|=(2597367227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132866219/10000000000 : ℝ)|^4353 ≤ (1326028641359/10000000000000 : ℝ)^3329
        have hw : |(-2132866219/10000000000 : ℝ)|=(2132866219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s2_3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861682091/2000000000 : ℝ)*x 0 + (503392603/1250000000 : ℝ)*x 1 + (1151874449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861682091/2000000000 : ℝ)^4353 ≤ (1330126780173/4000000000000 : ℝ)^3329 := by
    have hnat : (861682091 : ℕ)^4353*4000000000000^3329 ≤ 1330126780173^3329*2000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861682091 2000000000 1330126780173 4000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503392603/1250000000 : ℝ)^4353 ≤ (30443451233353/100000000000000 : ℝ)^3329 := by
    have hnat : (503392603 : ℕ)^4353*100000000000000^3329 ≤ 30443451233353^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503392603 1250000000 30443451233353 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1151874449/2500000000 : ℝ)^4353 ≤ (18151689618339/50000000000000 : ℝ)^3329 := by
    have hnat : (1151874449 : ℕ)^4353*50000000000000^3329 ≤ 18151689618339^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1151874449 2500000000 18151689618339 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861682091/2000000000 : ℝ), (503392603/1250000000 : ℝ), (1151874449/2500000000 : ℝ)] ![(1330126780173/4000000000000 : ℝ), (30443451233353/100000000000000 : ℝ), (18151689618339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861682091/2000000000 : ℝ)|^4353 ≤ (1330126780173/4000000000000 : ℝ)^3329
        have hw : |(861682091/2000000000 : ℝ)|=(861682091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503392603/1250000000 : ℝ)|^4353 ≤ (30443451233353/100000000000000 : ℝ)^3329
        have hw : |(503392603/1250000000 : ℝ)|=(503392603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1151874449/2500000000 : ℝ)|^4353 ≤ (18151689618339/50000000000000 : ℝ)^3329
        have hw : |(1151874449/2500000000 : ℝ)|=(1151874449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s2_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1992819937/10000000000 : ℝ)*x 0 + (649543539/1250000000 : ℝ)*x 1 + (683119727/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1992819937/10000000000 : ℝ)^4353 ≤ (6066727987217/50000000000000 : ℝ)^3329 := by
    have hnat : (1992819937 : ℕ)^4353*50000000000000^3329 ≤ 6066727987217^3329*10000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992819937 10000000000 6066727987217 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649543539/1250000000 : ℝ)^4353 ≤ (5310764999231/12500000000000 : ℝ)^3329 := by
    have hnat : (649543539 : ℕ)^4353*12500000000000^3329 ≤ 5310764999231^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649543539 1250000000 5310764999231 12500000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683119727/1250000000 : ℝ)^4353 ≤ (22690212010847/50000000000000 : ℝ)^3329 := by
    have hnat : (683119727 : ℕ)^4353*50000000000000^3329 ≤ 22690212010847^3329*1250000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683119727 1250000000 22690212010847 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1992819937/10000000000 : ℝ), (649543539/1250000000 : ℝ), (683119727/1250000000 : ℝ)] ![(6066727987217/50000000000000 : ℝ), (5310764999231/12500000000000 : ℝ), (22690212010847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1992819937/10000000000 : ℝ)|^4353 ≤ (6066727987217/50000000000000 : ℝ)^3329
        have hw : |(-1992819937/10000000000 : ℝ)|=(1992819937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649543539/1250000000 : ℝ)|^4353 ≤ (5310764999231/12500000000000 : ℝ)^3329
        have hw : |(649543539/1250000000 : ℝ)|=(649543539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683119727/1250000000 : ℝ)|^4353 ≤ (22690212010847/50000000000000 : ℝ)^3329
        have hw : |(683119727/1250000000 : ℝ)|=(683119727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s2_5 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646014627/5000000000 : ℝ)*x 0 + (-931321659/5000000000 : ℝ)*x 1 + (2732478753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646014627/5000000000 : ℝ)^4353 ≤ (4351194224583/10000000000000 : ℝ)^3329 := by
    have hnat : (2646014627 : ℕ)^4353*10000000000000^3329 ≤ 4351194224583^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646014627 5000000000 4351194224583 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (931321659/5000000000 : ℝ)^4353 ≤ (1110763708553/10000000000000 : ℝ)^3329 := by
    have hnat : (931321659 : ℕ)^4353*10000000000000^3329 ≤ 1110763708553^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931321659 5000000000 1110763708553 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732478753/5000000000 : ℝ)^4353 ≤ (45380420655661/100000000000000 : ℝ)^3329 := by
    have hnat : (2732478753 : ℕ)^4353*100000000000000^3329 ≤ 45380420655661^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732478753 5000000000 45380420655661 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646014627/5000000000 : ℝ), (-931321659/5000000000 : ℝ), (2732478753/5000000000 : ℝ)] ![(4351194224583/10000000000000 : ℝ), (1110763708553/10000000000000 : ℝ), (45380420655661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646014627/5000000000 : ℝ)|^4353 ≤ (4351194224583/10000000000000 : ℝ)^3329
        have hw : |(2646014627/5000000000 : ℝ)|=(2646014627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-931321659/5000000000 : ℝ)|^4353 ≤ (1110763708553/10000000000000 : ℝ)^3329
        have hw : |(-931321659/5000000000 : ℝ)|=(931321659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732478753/5000000000 : ℝ)|^4353 ≤ (45380420655661/100000000000000 : ℝ)^3329
        have hw : |(2732478753/5000000000 : ℝ)|=(2732478753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646015341/5000000000 : ℝ)*x 0 + (546495751/1000000000 : ℝ)*x 1 + (-931320671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646015341/5000000000 : ℝ)^4353 ≤ (10877989399673/25000000000000 : ℝ)^3329 := by
    have hnat : (2646015341 : ℕ)^4353*25000000000000^3329 ≤ 10877989399673^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646015341 5000000000 10877989399673 25000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546495751/1000000000 : ℝ)^4353 ≤ (22690210349547/50000000000000 : ℝ)^3329 := by
    have hnat : (546495751 : ℕ)^4353*50000000000000^3329 ≤ 22690210349547^3329*1000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546495751 1000000000 22690210349547 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931320671/5000000000 : ℝ)^4353 ≤ (5553810838633/50000000000000 : ℝ)^3329 := by
    have hnat : (931320671 : ℕ)^4353*50000000000000^3329 ≤ 5553810838633^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931320671 5000000000 5553810838633 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646015341/5000000000 : ℝ), (546495751/1000000000 : ℝ), (-931320671/5000000000 : ℝ)] ![(10877989399673/25000000000000 : ℝ), (22690210349547/50000000000000 : ℝ), (5553810838633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646015341/5000000000 : ℝ)|^4353 ≤ (10877989399673/25000000000000 : ℝ)^3329
        have hw : |(2646015341/5000000000 : ℝ)|=(2646015341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546495751/1000000000 : ℝ)|^4353 ≤ (22690210349547/50000000000000 : ℝ)^3329
        have hw : |(546495751/1000000000 : ℝ)|=(546495751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-931320671/5000000000 : ℝ)|^4353 ≤ (5553810838633/50000000000000 : ℝ)^3329
        have hw : |(-931320671/5000000000 : ℝ)|=(931320671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1393_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269282749/625000000 : ℝ)*x 0 + (2302026347/5000000000 : ℝ)*x 1 + (1007653701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269282749/625000000 : ℝ)^4353 ≤ (3325431527953/10000000000000 : ℝ)^3329 := by
    have hnat : (269282749 : ℕ)^4353*10000000000000^3329 ≤ 3325431527953^3329*625000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269282749 625000000 3325431527953 10000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2302026347/5000000000 : ℝ)^4353 ≤ (36267888998153/100000000000000 : ℝ)^3329 := by
    have hnat : (2302026347 : ℕ)^4353*100000000000000^3329 ≤ 36267888998153^3329*5000000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302026347 5000000000 36267888998153 100000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007653701/2500000000 : ℝ)^4353 ≤ (15238897853247/50000000000000 : ℝ)^3329 := by
    have hnat : (1007653701 : ℕ)^4353*50000000000000^3329 ≤ 15238897853247^3329*2500000000^4353 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007653701 2500000000 15238897853247 50000000000000 4353 3329 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4353/1024 : ℝ)) 4353 3329 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269282749/625000000 : ℝ), (2302026347/5000000000 : ℝ), (1007653701/2500000000 : ℝ)] ![(3325431527953/10000000000000 : ℝ), (36267888998153/100000000000000 : ℝ), (15238897853247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269282749/625000000 : ℝ)|^4353 ≤ (3325431527953/10000000000000 : ℝ)^3329
        have hw : |(269282749/625000000 : ℝ)|=(269282749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2302026347/5000000000 : ℝ)|^4353 ≤ (36267888998153/100000000000000 : ℝ)^3329
        have hw : |(2302026347/5000000000 : ℝ)|=(2302026347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007653701/2500000000 : ℝ)|^4353 ≤ (15238897853247/50000000000000 : ℝ)^3329
        have hw : |(1007653701/2500000000 : ℝ)|=(1007653701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1393_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4773/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3979/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4773/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4773/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4773/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4773/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4773/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4773/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7347/100000 : ℝ) ^ (17/4 : ℝ) ≤ (1896171795269/125000000000000000 : ℝ) := by
    have hpowers : (7347/100000 : ℝ)^17 ≤ (1896171795269/125000000000000000 : ℝ)^4 := by
      have hnat : (7347 : ℕ)^17*125000000000000000^4 ≤ 1896171795269^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7347 100000 1896171795269 125000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7347/100000 : ℝ)) (X := (1896171795269/125000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hpowhi : (4773/25000 : ℝ) ^ (17/4 : ℝ) ≤ (3513003241550097/4000000000000000000 : ℝ) := by
    have hpowers : (4773/25000 : ℝ)^17 ≤ (3513003241550097/4000000000000000000 : ℝ)^4 := by
      have hnat : (4773 : ℕ)^17*4000000000000000000^4 ≤ 3513003241550097^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4773 25000 3513003241550097 4000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4773/25000 : ℝ)) (X := (3513003241550097/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner00 : (62501896171795269/62500000000000000 : ℝ) ≤ (5000035692231527/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (62501896171795269/62500000000000000 : ℝ)^4 ≤ (5000035692231527/5000000000000000 : ℝ)^17 := by
      have hnat : (62501896171795269 : ℕ)^4*5000000000000000^17 ≤ 5000035692231527^17*62500000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62501896171795269 62500000000000000 5000035692231527 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000035692231527/5000000000000000 : ℝ)) (X := (62501896171795269/62500000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner10 : (800714736147799741/800000000000000000 : ℝ) ≤ (5001050723707139/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (800714736147799741/800000000000000000 : ℝ)^4 ≤ (5001050723707139/5000000000000000 : ℝ)^17 := by
      have hnat : (800714736147799741 : ℕ)^4*5000000000000000^17 ≤ 5001050723707139^17*800000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800714736147799741 800000000000000000 5001050723707139 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001050723707139/5000000000000000 : ℝ)) (X := (800714736147799741/800000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have hcorner11 : (2003513003241550097/2000000000000000000 : ℝ) ≤ (5002065755182751/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2003513003241550097/2000000000000000000 : ℝ)^4 ≤ (5002065755182751/5000000000000000 : ℝ)^17 := by
      have hnat : (2003513003241550097 : ℕ)^4*5000000000000000^17 ≤ 5002065755182751^17*2000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2003513003241550097 2000000000000000000 5002065755182751 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002065755182751/5000000000000000 : ℝ)) (X := (2003513003241550097/2000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1896171795269/125000000000000000 : ℝ) ≤ ((724821041145143727/725000000000000000 : ℝ)+2*(9398439589/5437500000000 : ℝ)*(7347/100000 : ℝ))^(17/4 : ℝ) := by
    rw [show (724821041145143727/725000000000000000 : ℝ)+2*(9398439589/5437500000000 : ℝ)*(7347/100000 : ℝ)=(5000035692231527/5000000000000000 : ℝ) by norm_num, show 1+2*(1896171795269/125000000000000000 : ℝ)=(62501896171795269/62500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3513003241550097/4000000000000000000 : ℝ)+(1896171795269/125000000000000000 : ℝ) ≤ ((724821041145143727/725000000000000000 : ℝ)+(9398439589/5437500000000 : ℝ)*((4773/25000 : ℝ)+(7347/100000 : ℝ)))^(17/4 : ℝ) := by
    rw [show (724821041145143727/725000000000000000 : ℝ)+(9398439589/5437500000000 : ℝ)*((4773/25000 : ℝ)+(7347/100000 : ℝ))=(5001050723707139/5000000000000000 : ℝ) by norm_num, show 1+(3513003241550097/4000000000000000000 : ℝ)+(1896171795269/125000000000000000 : ℝ)=(800714736147799741/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3513003241550097/4000000000000000000 : ℝ) ≤ ((724821041145143727/725000000000000000 : ℝ)+2*(9398439589/5437500000000 : ℝ)*(4773/25000 : ℝ))^(17/4 : ℝ) := by
    rw [show (724821041145143727/725000000000000000 : ℝ)+2*(9398439589/5437500000000 : ℝ)*(4773/25000 : ℝ)=(5002065755182751/5000000000000000 : ℝ) by norm_num, show 1+2*(3513003241550097/4000000000000000000 : ℝ)=(2003513003241550097/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (724821041145143727/725000000000000000 : ℝ)*(X 1 0+X 2 0)+(9398439589/5437500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (7347/100000 : ℝ)) (hi := (4773/25000 : ℝ)) (c := (724821041145143727/725000000000000000 : ℝ)) (alpha := (9398439589/5437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (724821041145143727/725000000000000000 : ℝ)*(X 0 1+X 2 1)+(9398439589/5437500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (7347/100000 : ℝ)) (hi := (4773/25000 : ℝ)) (c := (724821041145143727/725000000000000000 : ℝ)) (alpha := (9398439589/5437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (724821041145143727/725000000000000000 : ℝ)*(X 0 2+X 1 2)+(9398439589/5437500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (17/4 : ℝ)) (lo := (7347/100000 : ℝ)) (hi := (4773/25000 : ℝ)) (c := (724821041145143727/725000000000000000 : ℝ)) (alpha := (9398439589/5437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1992767409/10000000000 : ℝ)*X 0 0+(109331707/200000000 : ℝ)*X 0 1+(649341789/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((670309107/1250000000 : ℝ)*X 1 0+(-1066433119/5000000000 : ℝ)*X 1 1+(5194734269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362472687/10000000000 : ℝ)*X 2 0+(2597367227/5000000000 : ℝ)*X 2 1+(-2132866219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861682091/2000000000 : ℝ)*X 0 0+(503392603/1250000000 : ℝ)*X 0 1+(1151874449/2500000000 : ℝ)*X 0 2+(861682091/2000000000 : ℝ)*X 1 0+(503392603/1250000000 : ℝ)*X 1 1+(1151874449/2500000000 : ℝ)*X 1 2+(861682091/2000000000 : ℝ)*X 2 0+(503392603/1250000000 : ℝ)*X 2 1+(1151874449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1992819937/10000000000 : ℝ)*X 0 0+(649543539/1250000000 : ℝ)*X 0 1+(683119727/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646014627/5000000000 : ℝ)*X 1 0+(-931321659/5000000000 : ℝ)*X 1 1+(2732478753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646015341/5000000000 : ℝ)*X 2 0+(546495751/1000000000 : ℝ)*X 2 1+(-931320671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269282749/625000000 : ℝ)*X 0 0+(2302026347/5000000000 : ℝ)*X 0 1+(1007653701/2500000000 : ℝ)*X 0 2+(269282749/625000000 : ℝ)*X 1 0+(2302026347/5000000000 : ℝ)*X 1 1+(1007653701/2500000000 : ℝ)*X 1 2+(269282749/625000000 : ℝ)*X 2 0+(2302026347/5000000000 : ℝ)*X 2 1+(1007653701/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1393_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114961909668493271081599183/36250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63452987/12500000000000 : ℝ)*(base19) + (7471733/2500000000000 : ℝ)*(base23) + (6222189/12500000000000 : ℝ)*(lower2) + (29345749/25000000000000 : ℝ)*(upper3) + (35638013/100000000000000 : ℝ)*(upper5) + (675197284448389/25000000000000 : ℝ)*(major0) + (675197284448389/25000000000000 : ℝ)*(major1) + (2700789137793557/100000000000000 : ℝ)*(major2) + (919622748965857/25000000000000 : ℝ)*(sp0) + (73569891716393/2000000000000 : ℝ)*(sp1) + (1839247397287113/50000000000000 : ℝ)*(sp2) + (107692490830961/6250000000000 : ℝ)*(sp3) + (2048790059/50000000000000 : ℝ)*(sp4) + (644627217/20000000000000 : ℝ)*(sp7) + (1723083076431461/100000000000000 : ℝ)*(f.failure) + (1839247546721773/50000000000000 : ℝ)*(f.sum) + (1557025325937/362500000000000000000000000 : ℝ)*base66 + (15987989506867409/54375000000000000000000000000000 : ℝ)*base67 + (1617585579102300817/217500000000000000000000000000000 : ℝ)*base69 + (155869944886882591/54375000000000000000000000000000 : ℝ)*base72 + (70734519713/362500000000000000000000000 : ℝ)*base73 + (473374188447300817/217500000000000000000000000000000 : ℝ)*base75 + (541934040717032591/54375000000000000000000000000000 : ℝ)*base78 + (96450674950467409/54375000000000000000000000000000 : ℝ)*base79 + (3684057624511/1087500000000000000000000000 : ℝ)*base81 + (8385487/10000000000000000000000 : ℝ)*base89 + (8385487/10000000000000000000000 : ℝ)*base91 + (91614513/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (407266545128979676023/145000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258098819/50000000000000 : ℝ)*(base19) + (523692307/25000000000000 : ℝ)*(base23) + (56506789/50000000000000 : ℝ)*(lower2) + (23737711/20000000000000 : ℝ)*(upper3) + (177158679/100000000000000 : ℝ)*(lower4) + (8541802061797/312500000000 : ℝ)*(major0) + (8541802061797/312500000000 : ℝ)*(major1) + (8541802061797/312500000000 : ℝ)*(major2) + (8503899867/25000000000000 : ℝ)*(sp2) + (163920849/20000000000000 : ℝ)*(sp3) + (1861439778268081/50000000000000 : ℝ)*(sp4) + (930719760084631/25000000000000 : ℝ)*(sp5) + (1861421723083733/50000000000000 : ℝ)*(sp6) + (1743872849785171/100000000000000 : ℝ)*(sp7) + (217984208673677/12500000000000 : ℝ)*(f.failure) + (1861439778268081/50000000000000 : ℝ)*(f.sum) + (870334917379/435000000000000000000000000 : ℝ)*base66 + (1896106571047691/339843750000000000000000000000 : ℝ)*base67 + (149023201857743/679687500000000000000000000000 : ℝ)*base70 + (17454376813581389/1359375000000000000000000000000 : ℝ)*base71 + (416474416187/217500000000000000000000000 : ℝ)*base74 + (7697781395795243/679687500000000000000000000000 : ℝ)*base76 + (8907630798668611/1359375000000000000000000000000 : ℝ)*base78 + (83033208253919/5310058593750000000000000000 : ℝ)*base79 + (4063672261/6796875000000000000000000 : ℝ)*base82 + (8000441/1250000000000000000000 : ℝ)*base90 + (8000441/1250000000000000000000 : ℝ)*base92 + (8000441/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1393_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4773/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3979/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1393_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1393_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3979/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1393_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1393_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1393_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (4353/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156741667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3979/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1393_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
