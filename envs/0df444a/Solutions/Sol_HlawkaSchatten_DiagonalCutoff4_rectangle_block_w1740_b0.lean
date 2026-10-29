-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1740_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:07.943646+00:00
-- url     : https://prove2.me/submissions/f451b76d-bd1e-44b6-be35-ed902a08be22

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
theorem support_rectangle_w1740_s0_0 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-613347157/5000000000 : ℝ)*x 0 + (2831286747/5000000000 : ℝ)*x 1 + (4961819533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (613347157/5000000000 : ℝ)^5615 ≤ (7682162181757/100000000000000 : ℝ)^4591 := by
    have hnat : (613347157 : ℕ)^5615*100000000000000^4591 ≤ 7682162181757^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613347157 5000000000 7682162181757 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2831286747/5000000000 : ℝ)^5615 ≤ (49879811605597/100000000000000 : ℝ)^4591 := by
    have hnat : (2831286747 : ℕ)^5615*100000000000000^4591 ≤ 49879811605597^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831286747 5000000000 49879811605597 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4961819533/10000000000 : ℝ)^5615 ≤ (21219013096011/50000000000000 : ℝ)^4591 := by
    have hnat : (4961819533 : ℕ)^5615*50000000000000^4591 ≤ 21219013096011^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4961819533 10000000000 21219013096011 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-613347157/5000000000 : ℝ), (2831286747/5000000000 : ℝ), (4961819533/10000000000 : ℝ)] ![(7682162181757/100000000000000 : ℝ), (49879811605597/100000000000000 : ℝ), (21219013096011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-613347157/5000000000 : ℝ)|^5615 ≤ (7682162181757/100000000000000 : ℝ)^4591
        have hw : |(-613347157/5000000000 : ℝ)|=(613347157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2831286747/5000000000 : ℝ)|^5615 ≤ (49879811605597/100000000000000 : ℝ)^4591
        have hw : |(2831286747/5000000000 : ℝ)|=(2831286747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4961819533/10000000000 : ℝ)|^5615 ≤ (21219013096011/50000000000000 : ℝ)^4591
        have hw : |(4961819533/10000000000 : ℝ)|=(4961819533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s0_1 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383803431/10000000000 : ℝ)*x 0 + (-80227917/500000000 : ℝ)*x 1 + (4961819877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383803431/10000000000 : ℝ)^5615 ≤ (5861651222521/12500000000000 : ℝ)^4591 := by
    have hnat : (5383803431 : ℕ)^5615*12500000000000^4591 ≤ 5861651222521^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383803431 10000000000 5861651222521 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80227917/500000000 : ℝ)^5615 ≤ (10668760412251/100000000000000 : ℝ)^4591 := by
    have hnat : (80227917 : ℕ)^5615*100000000000000^4591 ≤ 10668760412251^4591*500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80227917 500000000 10668760412251 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4961819877/10000000000 : ℝ)^5615 ≤ (4243802979047/10000000000000 : ℝ)^4591 := by
    have hnat : (4961819877 : ℕ)^5615*10000000000000^4591 ≤ 4243802979047^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4961819877 10000000000 4243802979047 10000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383803431/10000000000 : ℝ), (-80227917/500000000 : ℝ), (4961819877/10000000000 : ℝ)] ![(5861651222521/12500000000000 : ℝ), (10668760412251/100000000000000 : ℝ), (4243802979047/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383803431/10000000000 : ℝ)|^5615 ≤ (5861651222521/12500000000000 : ℝ)^4591
        have hw : |(5383803431/10000000000 : ℝ)|=(5383803431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80227917/500000000 : ℝ)|^5615 ≤ (10668760412251/100000000000000 : ℝ)^4591
        have hw : |(-80227917/500000000 : ℝ)|=(80227917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4961819877/10000000000 : ℝ)|^5615 ≤ (4243802979047/10000000000000 : ℝ)^4591
        have hw : |(4961819877/10000000000 : ℝ)|=(4961819877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s0_2 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691901243/5000000000 : ℝ)*x 0 + (2480910353/5000000000 : ℝ)*x 1 + (-100284907/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691901243/5000000000 : ℝ)^5615 ≤ (9378639942657/20000000000000 : ℝ)^4591 := by
    have hnat : (2691901243 : ℕ)^5615*20000000000000^4591 ≤ 9378639942657^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691901243 5000000000 9378639942657 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2480910353/5000000000 : ℝ)^5615 ≤ (42438038462309/100000000000000 : ℝ)^4591 := by
    have hnat : (2480910353 : ℕ)^5615*100000000000000^4591 ≤ 42438038462309^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480910353 5000000000 42438038462309 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100284907/625000000 : ℝ)^5615 ≤ (5334380905483/50000000000000 : ℝ)^4591 := by
    have hnat : (100284907 : ℕ)^5615*50000000000000^4591 ≤ 5334380905483^4591*625000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100284907 625000000 5334380905483 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691901243/5000000000 : ℝ), (2480910353/5000000000 : ℝ), (-100284907/625000000 : ℝ)] ![(9378639942657/20000000000000 : ℝ), (42438038462309/100000000000000 : ℝ), (5334380905483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691901243/5000000000 : ℝ)|^5615 ≤ (9378639942657/20000000000000 : ℝ)^4591
        have hw : |(2691901243/5000000000 : ℝ)|=(2691901243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2480910353/5000000000 : ℝ)|^5615 ≤ (42438038462309/100000000000000 : ℝ)^4591
        have hw : |(2480910353/5000000000 : ℝ)|=(2480910353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100284907/625000000 : ℝ)|^5615 ≤ (5334380905483/50000000000000 : ℝ)^4591
        have hw : |(-100284907/625000000 : ℝ)|=(100284907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s0_3 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (99813369/250000000 : ℝ)*x 0 + (2974864183/10000000000 : ℝ)*x 1 + (5183473511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99813369/250000000 : ℝ)^5615 ≤ (16265940999297/50000000000000 : ℝ)^4591 := by
    have hnat : (99813369 : ℕ)^5615*50000000000000^4591 ≤ 16265940999297^4591*250000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99813369 250000000 16265940999297 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2974864183/10000000000 : ℝ)^5615 ≤ (22700037534327/100000000000000 : ℝ)^4591 := by
    have hnat : (2974864183 : ℕ)^5615*100000000000000^4591 ≤ 22700037534327^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974864183 10000000000 22700037534327 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183473511/10000000000 : ℝ)^5615 ≤ (44768080454309/100000000000000 : ℝ)^4591 := by
    have hnat : (5183473511 : ℕ)^5615*100000000000000^4591 ≤ 44768080454309^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183473511 10000000000 44768080454309 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(99813369/250000000 : ℝ), (2974864183/10000000000 : ℝ), (5183473511/10000000000 : ℝ)] ![(16265940999297/50000000000000 : ℝ), (22700037534327/100000000000000 : ℝ), (44768080454309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(99813369/250000000 : ℝ)|^5615 ≤ (16265940999297/50000000000000 : ℝ)^4591
        have hw : |(99813369/250000000 : ℝ)|=(99813369/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2974864183/10000000000 : ℝ)|^5615 ≤ (22700037534327/100000000000000 : ℝ)^4591
        have hw : |(2974864183/10000000000 : ℝ)|=(2974864183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183473511/10000000000 : ℝ)|^5615 ≤ (44768080454309/100000000000000 : ℝ)^4591
        have hw : |(5183473511/10000000000 : ℝ)|=(5183473511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s0_4 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1228287569/10000000000 : ℝ)*x 0 + (4979959873/10000000000 : ℝ)*x 1 + (5643812879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1228287569/10000000000 : ℝ)^5615 ≤ (3847183590517/50000000000000 : ℝ)^4591 := by
    have hnat : (1228287569 : ℕ)^5615*50000000000000^4591 ≤ 3847183590517^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228287569 10000000000 3847183590517 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979959873/10000000000 : ℝ)^5615 ≤ (2664241397859/6250000000000 : ℝ)^4591 := by
    have hnat : (4979959873 : ℕ)^5615*6250000000000^4591 ≤ 2664241397859^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979959873 10000000000 2664241397859 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5643812879/10000000000 : ℝ)^5615 ≤ (6209721305361/12500000000000 : ℝ)^4591 := by
    have hnat : (5643812879 : ℕ)^5615*12500000000000^4591 ≤ 6209721305361^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643812879 10000000000 6209721305361 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1228287569/10000000000 : ℝ), (4979959873/10000000000 : ℝ), (5643812879/10000000000 : ℝ)] ![(3847183590517/50000000000000 : ℝ), (2664241397859/6250000000000 : ℝ), (6209721305361/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1228287569/10000000000 : ℝ)|^5615 ≤ (3847183590517/50000000000000 : ℝ)^4591
        have hw : |(-1228287569/10000000000 : ℝ)|=(1228287569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4979959873/10000000000 : ℝ)|^5615 ≤ (2664241397859/6250000000000 : ℝ)^4591
        have hw : |(4979959873/10000000000 : ℝ)|=(4979959873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5643812879/10000000000 : ℝ)|^5615 ≤ (6209721305361/12500000000000 : ℝ)^4591
        have hw : |(5643812879/10000000000 : ℝ)|=(5643812879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s0_5 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103919929/200000000 : ℝ)*x 0 + (-922566471/10000000000 : ℝ)*x 1 + (705476703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103919929/200000000 : ℝ)^5615 ≤ (44900396723327/100000000000000 : ℝ)^4591 := by
    have hnat : (103919929 : ℕ)^5615*100000000000000^4591 ≤ 44900396723327^4591*200000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103919929 200000000 44900396723327 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922566471/10000000000 : ℝ)^5615 ≤ (216872992241/4000000000000 : ℝ)^4591 := by
    have hnat : (922566471 : ℕ)^5615*4000000000000^4591 ≤ 216872992241^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922566471 10000000000 216872992241 4000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705476703/1250000000 : ℝ)^5615 ≤ (6209722307893/12500000000000 : ℝ)^4591 := by
    have hnat : (705476703 : ℕ)^5615*12500000000000^4591 ≤ 6209722307893^4591*1250000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705476703 1250000000 6209722307893 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103919929/200000000 : ℝ), (-922566471/10000000000 : ℝ), (705476703/1250000000 : ℝ)] ![(44900396723327/100000000000000 : ℝ), (216872992241/4000000000000 : ℝ), (6209722307893/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103919929/200000000 : ℝ)|^5615 ≤ (44900396723327/100000000000000 : ℝ)^4591
        have hw : |(103919929/200000000 : ℝ)|=(103919929/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-922566471/10000000000 : ℝ)|^5615 ≤ (216872992241/4000000000000 : ℝ)^4591
        have hw : |(-922566471/10000000000 : ℝ)|=(922566471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(705476703/1250000000 : ℝ)|^5615 ≤ (6209722307893/12500000000000 : ℝ)^4591
        have hw : |(705476703/1250000000 : ℝ)|=(705476703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s0_6 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195997739/10000000000 : ℝ)*x 0 + (5643812283/10000000000 : ℝ)*x 1 + (-461283291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195997739/10000000000 : ℝ)^5615 ≤ (11225102586613/25000000000000 : ℝ)^4591 := by
    have hnat : (5195997739 : ℕ)^5615*25000000000000^4591 ≤ 11225102586613^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195997739 10000000000 11225102586613 25000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5643812283/10000000000 : ℝ)^5615 ≤ (49677764026683/100000000000000 : ℝ)^4591 := by
    have hnat : (5643812283 : ℕ)^5615*100000000000000^4591 ≤ 49677764026683^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643812283 10000000000 49677764026683 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461283291/5000000000 : ℝ)^5615 ≤ (271091280193/5000000000000 : ℝ)^4591 := by
    have hnat : (461283291 : ℕ)^5615*5000000000000^4591 ≤ 271091280193^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461283291 5000000000 271091280193 5000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195997739/10000000000 : ℝ), (5643812283/10000000000 : ℝ), (-461283291/5000000000 : ℝ)] ![(11225102586613/25000000000000 : ℝ), (49677764026683/100000000000000 : ℝ), (271091280193/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195997739/10000000000 : ℝ)|^5615 ≤ (11225102586613/25000000000000 : ℝ)^4591
        have hw : |(5195997739/10000000000 : ℝ)|=(5195997739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5643812283/10000000000 : ℝ)|^5615 ≤ (49677764026683/100000000000000 : ℝ)^4591
        have hw : |(5643812283/10000000000 : ℝ)|=(5643812283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-461283291/5000000000 : ℝ)|^5615 ≤ (271091280193/5000000000000 : ℝ)^4591
        have hw : |(-461283291/5000000000 : ℝ)|=(461283291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s0_7 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1998780697/5000000000 : ℝ)*x 0 + (5126302439/10000000000 : ℝ)*x 1 + (606798919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998780697/5000000000 : ℝ)^5615 ≤ (4072747799473/12500000000000 : ℝ)^4591 := by
    have hnat : (1998780697 : ℕ)^5615*12500000000000^4591 ≤ 4072747799473^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998780697 5000000000 4072747799473 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126302439/10000000000 : ℝ)^5615 ≤ (5520615439001/12500000000000 : ℝ)^4591 := by
    have hnat : (5126302439 : ℕ)^5615*12500000000000^4591 ≤ 5520615439001^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126302439 10000000000 5520615439001 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606798919/2000000000 : ℝ)^5615 ≤ (23253094081213/100000000000000 : ℝ)^4591 := by
    have hnat : (606798919 : ℕ)^5615*100000000000000^4591 ≤ 23253094081213^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606798919 2000000000 23253094081213 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1998780697/5000000000 : ℝ), (5126302439/10000000000 : ℝ), (606798919/2000000000 : ℝ)] ![(4072747799473/12500000000000 : ℝ), (5520615439001/12500000000000 : ℝ), (23253094081213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1998780697/5000000000 : ℝ)|^5615 ≤ (4072747799473/12500000000000 : ℝ)^4591
        have hw : |(1998780697/5000000000 : ℝ)|=(1998780697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126302439/10000000000 : ℝ)|^5615 ≤ (5520615439001/12500000000000 : ℝ)^4591
        have hw : |(5126302439/10000000000 : ℝ)|=(5126302439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(606798919/2000000000 : ℝ)|^5615 ≤ (23253094081213/100000000000000 : ℝ)^4591
        have hw : |(606798919/2000000000 : ℝ)|=(606798919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1740_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1259/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4281/20000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5599/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5599 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5599*1^1024 ≤ 0^1024*1^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5599/1024 : ℝ) ≤ (166760888177598667/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5599 ≤ (166760888177598667/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5599*25000000000000000000^1024 ≤ 166760888177598667^1024*5^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 166760888177598667 25000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (166760888177598667/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5599 := by
      have hnat : (1 : ℕ)^1024*1^5599 ≤ 1^5599*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25166760888177598667/25000000000000000000 : ℝ) ≤ (10012166433313311/10000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (25166760888177598667/25000000000000000000 : ℝ)^1024 ≤ (10012166433313311/10000000000000000 : ℝ)^5599 := by
      have hnat : (25166760888177598667 : ℕ)^1024*10000000000000000^5599 ≤ 10012166433313311^5599*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25166760888177598667 25000000000000000000 10012166433313311 10000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012166433313311/10000000000000000 : ℝ)) (X := (25166760888177598667/25000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12666760888177598667/12500000000000000000 : ℝ) ≤ (5012166433313311/5000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (12666760888177598667/12500000000000000000 : ℝ)^1024 ≤ (5012166433313311/5000000000000000 : ℝ)^5599 := by
      have hnat : (12666760888177598667 : ℕ)^1024*5000000000000000^5599 ≤ 5012166433313311^5599*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12666760888177598667 12500000000000000000 5012166433313311 5000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012166433313311/5000000000000000 : ℝ)) (X := (12666760888177598667/12500000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12166433313311/4000000000000000 : ℝ)*(0 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12166433313311/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(166760888177598667/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12166433313311/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5599/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12166433313311/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10012166433313311/10000000000000000 : ℝ) by norm_num, show 1+(166760888177598667/25000000000000000000 : ℝ)+(0 : ℝ)=(25166760888177598667/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(166760888177598667/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12166433313311/4000000000000000 : ℝ)*(2/5 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12166433313311/4000000000000000 : ℝ)*(2/5 : ℝ)=(5012166433313311/5000000000000000 : ℝ) by norm_num, show 1+2*(166760888177598667/25000000000000000000 : ℝ)=(12666760888177598667/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12166433313311/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12166433313311/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12166433313311/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12166433313311/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12166433313311/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12166433313311/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-613347157/5000000000 : ℝ)*X 0 0+(2831286747/5000000000 : ℝ)*X 0 1+(4961819533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5383803431/10000000000 : ℝ)*X 1 0+(-80227917/500000000 : ℝ)*X 1 1+(4961819877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2691901243/5000000000 : ℝ)*X 2 0+(2480910353/5000000000 : ℝ)*X 2 1+(-100284907/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((99813369/250000000 : ℝ)*X 0 0+(2974864183/10000000000 : ℝ)*X 0 1+(5183473511/10000000000 : ℝ)*X 0 2+(99813369/250000000 : ℝ)*X 1 0+(2974864183/10000000000 : ℝ)*X 1 1+(5183473511/10000000000 : ℝ)*X 1 2+(99813369/250000000 : ℝ)*X 2 0+(2974864183/10000000000 : ℝ)*X 2 1+(5183473511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1228287569/10000000000 : ℝ)*X 0 0+(4979959873/10000000000 : ℝ)*X 0 1+(5643812879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((103919929/200000000 : ℝ)*X 1 0+(-922566471/10000000000 : ℝ)*X 1 1+(705476703/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5195997739/10000000000 : ℝ)*X 2 0+(5643812283/10000000000 : ℝ)*X 2 1+(-461283291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1998780697/5000000000 : ℝ)*X 0 0+(5126302439/10000000000 : ℝ)*X 0 1+(606798919/2000000000 : ℝ)*X 0 2+(1998780697/5000000000 : ℝ)*X 1 0+(5126302439/10000000000 : ℝ)*X 1 1+(606798919/2000000000 : ℝ)*X 1 2+(1998780697/5000000000 : ℝ)*X 2 0+(5126302439/10000000000 : ℝ)*X 2 1+(606798919/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1505784956662901516395329/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10288183/20000000000000 : ℝ)*(base1) + (1633085781/100000000000000 : ℝ)*(base19) + (345650217/25000000000000 : ℝ)*(base23) + (332590291/100000000000000 : ℝ)*(upper3) + (42306911/20000000000000 : ℝ)*(upper5) + (939914471269529/100000000000000 : ℝ)*(major0) + (939914471269529/100000000000000 : ℝ)*(major1) + (939914471269529/100000000000000 : ℝ)*(major2) + (356760784860507/25000000000000 : ℝ)*(sp0) + (1427048988042047/100000000000000 : ℝ)*(sp1) + (17838115481587/1250000000000 : ℝ)*(sp2) + (452775619639419/100000000000000 : ℝ)*(sp3) + (3766563357/50000000000000 : ℝ)*(sp4) + (2399366729/100000000000000 : ℝ)*(sp7) + (56597258805883/12500000000000 : ℝ)*(f.failure) + (356762655281957/25000000000000 : ℝ)*(f.sum) + (385644462800519/200000000000000000000000000000 : ℝ)*base65 + (5679254039600519/400000000000000000000000000000 : ℝ)*base67 + (39748973199481/400000000000000000000000000000 : ℝ)*base70 + (2479216815200519/400000000000000000000000000000 : ℝ)*base71 + (1272096038800519/200000000000000000000000000000 : ℝ)*base73 + (259176751200519/400000000000000000000000000000 : ℝ)*base75 + (1033153094000519/400000000000000000000000000000 : ℝ)*base77 + (3511061797200519/400000000000000000000000000000 : ℝ)*base79 + (299027284399481/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2046227/625000000000000000000 : ℝ)*base89 + (2046227/625000000000000000000 : ℝ)*base91 + (2046227/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (571938194420658568379919/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (291840087/50000000000000 : ℝ)*(base19) + (497150749/50000000000000 : ℝ)*(base23) + (630616783/100000000000000 : ℝ)*(base32) + (81788891/100000000000000 : ℝ)*(base37) + (235563873/100000000000000 : ℝ)*(upper3) + (992147962308357/100000000000000 : ℝ)*(major0) + (992147962308357/100000000000000 : ℝ)*(major1) + (992147962308357/100000000000000 : ℝ)*(major2) + (479922171/25000000000000 : ℝ)*(sp1) + (14707483/500000000000 : ℝ)*(sp2) + (47073606819847/3125000000000 : ℝ)*(sp4) + (753176457433123/50000000000000 : ℝ)*(sp5) + (753175741218503/50000000000000 : ℝ)*(sp6) + (238969706341899/50000000000000 : ℝ)*(sp7) + (7467814454523/1562500000000 : ℝ)*(f.failure) + (47073606819847/3125000000000 : ℝ)*(f.sum) + (109295072559973/200000000000000000000000000000 : ℝ)*base66 + (2171733329040027/400000000000000000000000000000 : ℝ)*base67 + (2428528884240027/400000000000000000000000000000 : ℝ)*base69 + (170601008240027/400000000000000000000000000000 : ℝ)*base71 + (601375195440027/200000000000000000000000000000 : ℝ)*base73 + (2496287701840027/400000000000000000000000000000 : ℝ)*base75 + (484770796240027/400000000000000000000000000000 : ℝ)*base77 + (2433668326640027/400000000000000000000000000000 : ℝ)*base79 + (346743551040027/200000000000000000000000000000 : ℝ)*base81 + (829863/78125000000000000000 : ℝ)*base90 + (829863/78125000000000000000 : ℝ)*base92 + (829863/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1740_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4281/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1740_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1740_s1_0 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9989571/78125000 : ℝ)*x 0 + (344754571/625000000 : ℝ)*x 1 + (1014750289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9989571/78125000 : ℝ)^5615 ≤ (808208290263/10000000000000 : ℝ)^4591 := by
    have hnat : (9989571 : ℕ)^5615*10000000000000^4591 ≤ 808208290263^4591*78125000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9989571 78125000 808208290263 10000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344754571/625000000 : ℝ)^5615 ≤ (966121741319/2000000000000 : ℝ)^4591 := by
    have hnat : (344754571 : ℕ)^5615*2000000000000^4591 ≤ 966121741319^4591*625000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344754571 625000000 966121741319 2000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014750289/2000000000 : ℝ)^5615 ≤ (43611830023209/100000000000000 : ℝ)^4591 := by
    have hnat : (1014750289 : ℕ)^5615*100000000000000^4591 ≤ 43611830023209^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014750289 2000000000 43611830023209 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9989571/78125000 : ℝ), (344754571/625000000 : ℝ), (1014750289/2000000000 : ℝ)] ![(808208290263/10000000000000 : ℝ), (966121741319/2000000000000 : ℝ), (43611830023209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9989571/78125000 : ℝ)|^5615 ≤ (808208290263/10000000000000 : ℝ)^4591
        have hw : |(-9989571/78125000 : ℝ)|=(9989571/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344754571/625000000 : ℝ)|^5615 ≤ (966121741319/2000000000000 : ℝ)^4591
        have hw : |(344754571/625000000 : ℝ)|=(344754571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1014750289/2000000000 : ℝ)|^5615 ≤ (43611830023209/100000000000000 : ℝ)^4591
        have hw : |(1014750289/2000000000 : ℝ)|=(1014750289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s1_1 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167023669/312500000 : ℝ)*x 0 + (-302140481/2000000000 : ℝ)*x 1 + (2536875629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167023669/312500000 : ℝ)^5615 ≤ (23238798941991/50000000000000 : ℝ)^4591 := by
    have hnat : (167023669 : ℕ)^5615*50000000000000^4591 ≤ 23238798941991^4591*312500000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167023669 312500000 23238798941991 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302140481/2000000000 : ℝ)^5615 ≤ (9910574042829/100000000000000 : ℝ)^4591 := by
    have hnat : (302140481 : ℕ)^5615*100000000000000^4591 ≤ 9910574042829^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302140481 2000000000 9910574042829 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536875629/5000000000 : ℝ)^5615 ≤ (43611828057319/100000000000000 : ℝ)^4591 := by
    have hnat : (2536875629 : ℕ)^5615*100000000000000^4591 ≤ 43611828057319^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536875629 5000000000 43611828057319 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167023669/312500000 : ℝ), (-302140481/2000000000 : ℝ), (2536875629/5000000000 : ℝ)] ![(23238798941991/50000000000000 : ℝ), (9910574042829/100000000000000 : ℝ), (43611828057319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167023669/312500000 : ℝ)|^5615 ≤ (23238798941991/50000000000000 : ℝ)^4591
        have hw : |(167023669/312500000 : ℝ)|=(167023669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-302140481/2000000000 : ℝ)|^5615 ≤ (9910574042829/100000000000000 : ℝ)^4591
        have hw : |(-302140481/2000000000 : ℝ)|=(302140481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2536875629/5000000000 : ℝ)|^5615 ≤ (43611828057319/100000000000000 : ℝ)^4591
        have hw : |(2536875629/5000000000 : ℝ)|=(2536875629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s1_2 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336189233/2500000000 : ℝ)*x 0 + (5073751659/10000000000 : ℝ)*x 1 + (-151070251/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336189233/2500000000 : ℝ)^5615 ≤ (23238796410741/50000000000000 : ℝ)^4591 := by
    have hnat : (1336189233 : ℕ)^5615*50000000000000^4591 ≤ 23238796410741^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336189233 2500000000 23238796410741 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5073751659/10000000000 : ℝ)^5615 ≤ (2725739517059/6250000000000 : ℝ)^4591 := by
    have hnat : (5073751659 : ℕ)^5615*6250000000000^4591 ≤ 2725739517059^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073751659 10000000000 2725739517059 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151070251/1000000000 : ℝ)^5615 ≤ (9910574885293/100000000000000 : ℝ)^4591 := by
    have hnat : (151070251 : ℕ)^5615*100000000000000^4591 ≤ 9910574885293^4591*1000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151070251 1000000000 9910574885293 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336189233/2500000000 : ℝ), (5073751659/10000000000 : ℝ), (-151070251/1000000000 : ℝ)] ![(23238796410741/50000000000000 : ℝ), (2725739517059/6250000000000 : ℝ), (9910574885293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336189233/2500000000 : ℝ)|^5615 ≤ (23238796410741/50000000000000 : ℝ)^4591
        have hw : |(1336189233/2500000000 : ℝ)|=(1336189233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5073751659/10000000000 : ℝ)|^5615 ≤ (2725739517059/6250000000000 : ℝ)^4591
        have hw : |(5073751659/10000000000 : ℝ)|=(5073751659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-151070251/1000000000 : ℝ)|^5615 ≤ (9910574885293/100000000000000 : ℝ)^4591
        have hw : |(-151070251/1000000000 : ℝ)|=(151070251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s1_3 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2020509661/5000000000 : ℝ)*x 0 + (1689126441/5000000000 : ℝ)*x 1 + (1193086603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020509661/5000000000 : ℝ)^5615 ≤ (8253927878949/25000000000000 : ℝ)^4591 := by
    have hnat : (2020509661 : ℕ)^5615*25000000000000^4591 ≤ 8253927878949^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020509661 5000000000 8253927878949 25000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1689126441/5000000000 : ℝ)^5615 ≤ (26519739655383/100000000000000 : ℝ)^4591 := by
    have hnat : (1689126441 : ℕ)^5615*100000000000000^4591 ≤ 26519739655383^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689126441 5000000000 26519739655383 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193086603/2500000000 : ℝ)^5615 ≤ (2529034300283/6250000000000 : ℝ)^4591 := by
    have hnat : (1193086603 : ℕ)^5615*6250000000000^4591 ≤ 2529034300283^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193086603 2500000000 2529034300283 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2020509661/5000000000 : ℝ), (1689126441/5000000000 : ℝ), (1193086603/2500000000 : ℝ)] ![(8253927878949/25000000000000 : ℝ), (26519739655383/100000000000000 : ℝ), (2529034300283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2020509661/5000000000 : ℝ)|^5615 ≤ (8253927878949/25000000000000 : ℝ)^4591
        have hw : |(2020509661/5000000000 : ℝ)|=(2020509661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1689126441/5000000000 : ℝ)|^5615 ≤ (26519739655383/100000000000000 : ℝ)^4591
        have hw : |(1689126441/5000000000 : ℝ)|=(1689126441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193086603/2500000000 : ℝ)|^5615 ≤ (2529034300283/6250000000000 : ℝ)^4591
        have hw : |(1193086603/2500000000 : ℝ)|=(1193086603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s1_4 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1279064449/10000000000 : ℝ)*x 0 + (2540488777/5000000000 : ℝ)*x 1 + (1101738003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1279064449/10000000000 : ℝ)^5615 ≤ (1010646285019/12500000000000 : ℝ)^4591 := by
    have hnat : (1279064449 : ℕ)^5615*12500000000000^4591 ≤ 1010646285019^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279064449 10000000000 1010646285019 12500000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540488777/5000000000 : ℝ)^5615 ≤ (43687808581383/100000000000000 : ℝ)^4591 := by
    have hnat : (2540488777 : ℕ)^5615*100000000000000^4591 ≤ 43687808581383^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540488777 5000000000 43687808581383 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101738003/2000000000 : ℝ)^5615 ≤ (2411351056253/5000000000000 : ℝ)^4591 := by
    have hnat : (1101738003 : ℕ)^5615*5000000000000^4591 ≤ 2411351056253^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101738003 2000000000 2411351056253 5000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1279064449/10000000000 : ℝ), (2540488777/5000000000 : ℝ), (1101738003/2000000000 : ℝ)] ![(1010646285019/12500000000000 : ℝ), (43687808581383/100000000000000 : ℝ), (2411351056253/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1279064449/10000000000 : ℝ)|^5615 ≤ (1010646285019/12500000000000 : ℝ)^4591
        have hw : |(-1279064449/10000000000 : ℝ)|=(1279064449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540488777/5000000000 : ℝ)|^5615 ≤ (43687808581383/100000000000000 : ℝ)^4591
        have hw : |(2540488777/5000000000 : ℝ)|=(2540488777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101738003/2000000000 : ℝ)|^5615 ≤ (2411351056253/5000000000000 : ℝ)^4591
        have hw : |(1101738003/2000000000 : ℝ)|=(1101738003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s1_5 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227203559/10000000000 : ℝ)*x 0 + (-1075764863/10000000000 : ℝ)*x 1 + (2754344871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227203559/10000000000 : ℝ)^5615 ≤ (22615218780939/50000000000000 : ℝ)^4591 := by
    have hnat : (5227203559 : ℕ)^5615*50000000000000^4591 ≤ 22615218780939^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227203559 10000000000 22615218780939 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075764863/10000000000 : ℝ)^5615 ≤ (6542544227611/100000000000000 : ℝ)^4591 := by
    have hnat : (1075764863 : ℕ)^5615*100000000000000^4591 ≤ 6542544227611^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075764863 10000000000 6542544227611 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754344871/5000000000 : ℝ)^5615 ≤ (3014188637621/6250000000000 : ℝ)^4591 := by
    have hnat : (2754344871 : ℕ)^5615*6250000000000^4591 ≤ 3014188637621^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754344871 5000000000 3014188637621 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227203559/10000000000 : ℝ), (-1075764863/10000000000 : ℝ), (2754344871/5000000000 : ℝ)] ![(22615218780939/50000000000000 : ℝ), (6542544227611/100000000000000 : ℝ), (3014188637621/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227203559/10000000000 : ℝ)|^5615 ≤ (22615218780939/50000000000000 : ℝ)^4591
        have hw : |(5227203559/10000000000 : ℝ)|=(5227203559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075764863/10000000000 : ℝ)|^5615 ≤ (6542544227611/100000000000000 : ℝ)^4591
        have hw : |(-1075764863/10000000000 : ℝ)|=(1075764863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754344871/5000000000 : ℝ)|^5615 ≤ (3014188637621/6250000000000 : ℝ)^4591
        have hw : |(2754344871/5000000000 : ℝ)|=(2754344871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s1_6 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306800663/2500000000 : ℝ)*x 0 + (5508690591/10000000000 : ℝ)*x 1 + (-107576493/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306800663/2500000000 : ℝ)^5615 ≤ (45230427963207/100000000000000 : ℝ)^4591 := by
    have hnat : (1306800663 : ℕ)^5615*100000000000000^4591 ≤ 45230427963207^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306800663 2500000000 45230427963207 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508690591/10000000000 : ℝ)^5615 ≤ (4822702729253/10000000000000 : ℝ)^4591 := by
    have hnat : (5508690591 : ℕ)^5615*10000000000000^4591 ≤ 4822702729253^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508690591 10000000000 4822702729253 10000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107576493/1000000000 : ℝ)^5615 ≤ (261701789039/4000000000000 : ℝ)^4591 := by
    have hnat : (107576493 : ℕ)^5615*4000000000000^4591 ≤ 261701789039^4591*1000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107576493 1000000000 261701789039 4000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306800663/2500000000 : ℝ), (5508690591/10000000000 : ℝ), (-107576493/1000000000 : ℝ)] ![(45230427963207/100000000000000 : ℝ), (4822702729253/10000000000000 : ℝ), (261701789039/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306800663/2500000000 : ℝ)|^5615 ≤ (45230427963207/100000000000000 : ℝ)^4591
        have hw : |(1306800663/2500000000 : ℝ)|=(1306800663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508690591/10000000000 : ℝ)|^5615 ≤ (4822702729253/10000000000000 : ℝ)^4591
        have hw : |(5508690591/10000000000 : ℝ)|=(5508690591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-107576493/1000000000 : ℝ)|^5615 ≤ (261701789039/4000000000000 : ℝ)^4591
        have hw : |(-107576493/1000000000 : ℝ)|=(107576493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s1_7 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1010567377/2500000000 : ℝ)*x 0 + (4749567019/10000000000 : ℝ)*x 1 + (680304969/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010567377/2500000000 : ℝ)^5615 ≤ (33028204374147/100000000000000 : ℝ)^4591 := by
    have hnat : (1010567377 : ℕ)^5615*100000000000000^4591 ≤ 33028204374147^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010567377 2500000000 33028204374147 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4749567019/10000000000 : ℝ)^5615 ≤ (10057112223143/25000000000000 : ℝ)^4591 := by
    have hnat : (4749567019 : ℕ)^5615*25000000000000^4591 ≤ 10057112223143^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749567019 10000000000 10057112223143 25000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680304969/2000000000 : ℝ)^5615 ≤ (26743346715799/100000000000000 : ℝ)^4591 := by
    have hnat : (680304969 : ℕ)^5615*100000000000000^4591 ≤ 26743346715799^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680304969 2000000000 26743346715799 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1010567377/2500000000 : ℝ), (4749567019/10000000000 : ℝ), (680304969/2000000000 : ℝ)] ![(33028204374147/100000000000000 : ℝ), (10057112223143/25000000000000 : ℝ), (26743346715799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1010567377/2500000000 : ℝ)|^5615 ≤ (33028204374147/100000000000000 : ℝ)^4591
        have hw : |(1010567377/2500000000 : ℝ)|=(1010567377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4749567019/10000000000 : ℝ)|^5615 ≤ (10057112223143/25000000000000 : ℝ)^4591
        have hw : |(4749567019/10000000000 : ℝ)|=(4749567019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680304969/2000000000 : ℝ)|^5615 ≤ (26743346715799/100000000000000 : ℝ)^4591
        have hw : |(680304969/2000000000 : ℝ)|=(680304969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1740_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4281/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8809/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18281/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4281/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4281/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4281/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4281/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4281/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4281/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1259/20000 : ℝ) ^ (5599/1024 : ℝ) ≤ (13556600025717/50000000000000000000 : ℝ) := by
    have hpowers : (1259/20000 : ℝ)^5599 ≤ (13556600025717/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1259 : ℕ)^5599*50000000000000000000^1024 ≤ 13556600025717^1024*20000^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1259 20000 13556600025717 50000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1259/20000 : ℝ)) (X := (13556600025717/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4281/20000 : ℝ) ^ (5599/1024 : ℝ) ≤ (10923931646204409/50000000000000000000 : ℝ) := by
    have hpowers : (4281/20000 : ℝ)^5599 ≤ (10923931646204409/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4281 : ℕ)^5599*50000000000000000000^1024 ≤ 10923931646204409^1024*20000^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4281 20000 10923931646204409 50000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4281/20000 : ℝ)) (X := (10923931646204409/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000013556600025717/25000000000000000000 : ℝ) ≤ (10000000991745337/10000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (25000013556600025717/25000000000000000000 : ℝ)^1024 ≤ (10000000991745337/10000000000000000 : ℝ)^5599 := by
      have hnat : (25000013556600025717 : ℕ)^1024*10000000000000000^5599 ≤ 10000000991745337^5599*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000013556600025717 25000000000000000000 10000000991745337 10000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000991745337/10000000000000000 : ℝ)) (X := (25000013556600025717/25000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005468744123115063/25000000000000000000 : ℝ) ≤ (5000200017630629/5000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (25005468744123115063/25000000000000000000 : ℝ)^1024 ≤ (5000200017630629/5000000000000000 : ℝ)^5599 := by
      have hnat : (25005468744123115063 : ℕ)^1024*5000000000000000^5599 ≤ 5000200017630629^5599*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005468744123115063 25000000000000000000 5000200017630629 5000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000200017630629/5000000000000000 : ℝ)) (X := (25005468744123115063/25000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010923931646204409/25000000000000000000 : ℝ) ≤ (10000799078777179/10000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (25010923931646204409/25000000000000000000 : ℝ)^1024 ≤ (10000799078777179/10000000000000000 : ℝ)^5599 := by
      have hnat : (25010923931646204409 : ℕ)^1024*10000000000000000^5599 ≤ 10000799078777179^5599*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010923931646204409 25000000000000000000 10000799078777179 10000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000799078777179/10000000000000000 : ℝ)) (X := (25010923931646204409/25000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13556600025717/50000000000000000000 : ℝ) ≤ ((3777374775685164917/3777500000000000000 : ℝ)+2*(399043515921/1511000000000000 : ℝ)*(1259/20000 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (3777374775685164917/3777500000000000000 : ℝ)+2*(399043515921/1511000000000000 : ℝ)*(1259/20000 : ℝ)=(10000000991745337/10000000000000000 : ℝ) by norm_num, show 1+2*(13556600025717/50000000000000000000 : ℝ)=(25000013556600025717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10923931646204409/50000000000000000000 : ℝ)+(13556600025717/50000000000000000000 : ℝ) ≤ ((3777374775685164917/3777500000000000000 : ℝ)+(399043515921/1511000000000000 : ℝ)*((4281/20000 : ℝ)+(1259/20000 : ℝ)))^(5599/1024 : ℝ) := by
    rw [show (3777374775685164917/3777500000000000000 : ℝ)+(399043515921/1511000000000000 : ℝ)*((4281/20000 : ℝ)+(1259/20000 : ℝ))=(5000200017630629/5000000000000000 : ℝ) by norm_num, show 1+(10923931646204409/50000000000000000000 : ℝ)+(13556600025717/50000000000000000000 : ℝ)=(25005468744123115063/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10923931646204409/50000000000000000000 : ℝ) ≤ ((3777374775685164917/3777500000000000000 : ℝ)+2*(399043515921/1511000000000000 : ℝ)*(4281/20000 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (3777374775685164917/3777500000000000000 : ℝ)+2*(399043515921/1511000000000000 : ℝ)*(4281/20000 : ℝ)=(10000799078777179/10000000000000000 : ℝ) by norm_num, show 1+2*(10923931646204409/50000000000000000000 : ℝ)=(25010923931646204409/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3777374775685164917/3777500000000000000 : ℝ)*(X 1 0+X 2 0)+(399043515921/1511000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (1259/20000 : ℝ)) (hi := (4281/20000 : ℝ)) (c := (3777374775685164917/3777500000000000000 : ℝ)) (alpha := (399043515921/1511000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3777374775685164917/3777500000000000000 : ℝ)*(X 0 1+X 2 1)+(399043515921/1511000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (1259/20000 : ℝ)) (hi := (4281/20000 : ℝ)) (c := (3777374775685164917/3777500000000000000 : ℝ)) (alpha := (399043515921/1511000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3777374775685164917/3777500000000000000 : ℝ)*(X 0 2+X 1 2)+(399043515921/1511000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (1259/20000 : ℝ)) (hi := (4281/20000 : ℝ)) (c := (3777374775685164917/3777500000000000000 : ℝ)) (alpha := (399043515921/1511000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-9989571/78125000 : ℝ)*X 0 0+(344754571/625000000 : ℝ)*X 0 1+(1014750289/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167023669/312500000 : ℝ)*X 1 0+(-302140481/2000000000 : ℝ)*X 1 1+(2536875629/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336189233/2500000000 : ℝ)*X 2 0+(5073751659/10000000000 : ℝ)*X 2 1+(-151070251/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2020509661/5000000000 : ℝ)*X 0 0+(1689126441/5000000000 : ℝ)*X 0 1+(1193086603/2500000000 : ℝ)*X 0 2+(2020509661/5000000000 : ℝ)*X 1 0+(1689126441/5000000000 : ℝ)*X 1 1+(1193086603/2500000000 : ℝ)*X 1 2+(2020509661/5000000000 : ℝ)*X 2 0+(1689126441/5000000000 : ℝ)*X 2 1+(1193086603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1279064449/10000000000 : ℝ)*X 0 0+(2540488777/5000000000 : ℝ)*X 0 1+(1101738003/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5227203559/10000000000 : ℝ)*X 1 0+(-1075764863/10000000000 : ℝ)*X 1 1+(2754344871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1306800663/2500000000 : ℝ)*X 2 0+(5508690591/10000000000 : ℝ)*X 2 1+(-107576493/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1010567377/2500000000 : ℝ)*X 0 0+(4749567019/10000000000 : ℝ)*X 0 1+(680304969/2000000000 : ℝ)*X 0 2+(1010567377/2500000000 : ℝ)*X 1 0+(4749567019/10000000000 : ℝ)*X 1 1+(680304969/2000000000 : ℝ)*X 1 2+(1010567377/2500000000 : ℝ)*X 2 0+(4749567019/10000000000 : ℝ)*X 2 1+(680304969/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2084330365218485203458126909/188875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (872397667/50000000000000 : ℝ)*(base19) + (1360974363/100000000000000 : ℝ)*(base23) + (6095493/6250000000000 : ℝ)*(lower2) + (326402049/100000000000000 : ℝ)*(upper3) + (105008853/100000000000000 : ℝ)*(upper5) + (1489071366458341/100000000000000 : ℝ)*(major0) + (1489071366458341/100000000000000 : ℝ)*(major1) + (1489071366458341/100000000000000 : ℝ)*(major2) + (452162341129683/20000000000000 : ℝ)*(sp0) + (2260821246358127/100000000000000 : ℝ)*(sp1) + (2260821630179097/100000000000000 : ℝ)*(sp2) + (35865755452703/5000000000000 : ℝ)*(sp3) + (2257101009/20000000000000 : ℝ)*(sp4) + (4264859103/100000000000000 : ℝ)*(sp7) + (717319373913163/100000000000000 : ℝ)*(f.failure) + (113041149557673/5000000000000 : ℝ)*(f.sum) + (58133723966611/75550000000000000000000000000 : ℝ)*base65 + (1719572503358625197/377750000000000000000000000000000 : ℝ)*base67 + (2381761507499125197/377750000000000000000000000000000 : ℝ)*base69 + (111634541852124803/377750000000000000000000000000000 : ℝ)*base72 + (59166377403961/75550000000000000000000000000 : ℝ)*base73 + (977545979144874803/377750000000000000000000000000000 : ℝ)*base76 + (1101700124780875197/377750000000000000000000000000000 : ℝ)*base77 + (2766078806462875197/377750000000000000000000000000000 : ℝ)*base79 + (148528138065311/75550000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (18253453/5000000000000000000000 : ℝ)*base90 + (18253453/5000000000000000000000 : ℝ)*base92 + (18253453/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (231056711179670399615020359/37775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (583660377/100000000000000 : ℝ)*(base19) + (615465299/50000000000000 : ℝ)*(base23) + (552830147/100000000000000 : ℝ)*(upper2) + (2017887/20000000000000 : ℝ)*(upper3) + (143379281/25000000000000 : ℝ)*(upper5) + (307983389674203/20000000000000 : ℝ)*(major0) + (307983389674203/20000000000000 : ℝ)*(major1) + (307983389674203/20000000000000 : ℝ)*(major2) + (540945981/12500000000000 : ℝ)*(sp1) + (2060400473/50000000000000 : ℝ)*(sp2) + (292252606441427/12500000000000 : ℝ)*(sp4) + (2338015940303191/100000000000000 : ℝ)*(sp5) + (36531492184373/1562500000000 : ℝ)*(sp6) + (741812841322047/100000000000000 : ℝ)*(sp7) + (741812841322047/100000000000000 : ℝ)*(f.failure) + (292252606441427/12500000000000 : ℝ)*(f.sum) + (9362604334157/15110000000000000000000000000 : ℝ)*base66 + (570394696500906349/75550000000000000000000000000000 : ℝ)*base68 + (542680281879806349/75550000000000000000000000000000 : ℝ)*base70 + (420164524200506349/75550000000000000000000000000000 : ℝ)*base72 + (5960408467763/15110000000000000000000000000 : ℝ)*base73 + (295171551376106349/75550000000000000000000000000000 : ℝ)*base76 + (583234927830156349/75550000000000000000000000000000 : ℝ)*base78 + (738405604667006349/75550000000000000000000000000000 : ℝ)*base80 + (31674928688513/15110000000000000000000000000 : ℝ)*base81 + (20256057/5000000000000000000000 : ℝ)*base90 + (20256057/5000000000000000000000 : ℝ)*base92 + (20256057/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1740_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4281/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18281/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1740_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1740_s2_0 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1280252253/10000000000 : ℝ)*x 0 + (1377751461/2500000000 : ℝ)*x 1 + (2538872969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1280252253/10000000000 : ℝ)^5615 ≤ (2023588554621/25000000000000 : ℝ)^4591 := by
    have hnat : (1280252253 : ℕ)^5615*25000000000000^4591 ≤ 2023588554621^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280252253 10000000000 2023588554621 25000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377751461/2500000000 : ℝ)^5615 ≤ (48251818825961/100000000000000 : ℝ)^4591 := by
    have hnat : (1377751461 : ℕ)^5615*100000000000000^4591 ≤ 48251818825961^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377751461 2500000000 48251818825961 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538872969/5000000000 : ℝ)^5615 ≤ (1364182091781/3125000000000 : ℝ)^4591 := by
    have hnat : (2538872969 : ℕ)^5615*3125000000000^4591 ≤ 1364182091781^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538872969 5000000000 1364182091781 3125000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1280252253/10000000000 : ℝ), (1377751461/2500000000 : ℝ), (2538872969/5000000000 : ℝ)] ![(2023588554621/25000000000000 : ℝ), (48251818825961/100000000000000 : ℝ), (1364182091781/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1280252253/10000000000 : ℝ)|^5615 ≤ (2023588554621/25000000000000 : ℝ)^4591
        have hw : |(-1280252253/10000000000 : ℝ)|=(1280252253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1377751461/2500000000 : ℝ)|^5615 ≤ (48251818825961/100000000000000 : ℝ)^4591
        have hw : |(1377751461/2500000000 : ℝ)|=(1377751461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538872969/5000000000 : ℝ)|^5615 ≤ (1364182091781/3125000000000 : ℝ)^4591
        have hw : |(2538872969/5000000000 : ℝ)|=(2538872969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s2_1 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343362833/10000000000 : ℝ)*x 0 + (-1507315741/10000000000 : ℝ)*x 1 + (1015549163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343362833/10000000000 : ℝ)^5615 ≤ (2903922894079/6250000000000 : ℝ)^4591 := by
    have hnat : (5343362833 : ℕ)^5615*6250000000000^4591 ≤ 2903922894079^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343362833 10000000000 2903922894079 6250000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507315741/10000000000 : ℝ)^5615 ≤ (9883408035423/100000000000000 : ℝ)^4591 := by
    have hnat : (1507315741 : ℕ)^5615*100000000000000^4591 ≤ 9883408035423^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507315741 10000000000 9883408035423 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015549163/2000000000 : ℝ)^5615 ≤ (43653825643693/100000000000000 : ℝ)^4591 := by
    have hnat : (1015549163 : ℕ)^5615*100000000000000^4591 ≤ 43653825643693^4591*2000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015549163 2000000000 43653825643693 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343362833/10000000000 : ℝ), (-1507315741/10000000000 : ℝ), (1015549163/2000000000 : ℝ)] ![(2903922894079/6250000000000 : ℝ), (9883408035423/100000000000000 : ℝ), (43653825643693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343362833/10000000000 : ℝ)|^5615 ≤ (2903922894079/6250000000000 : ℝ)^4591
        have hw : |(5343362833/10000000000 : ℝ)|=(5343362833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1507315741/10000000000 : ℝ)|^5615 ≤ (9883408035423/100000000000000 : ℝ)^4591
        have hw : |(-1507315741/10000000000 : ℝ)|=(1507315741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015549163/2000000000 : ℝ)|^5615 ≤ (43653825643693/100000000000000 : ℝ)^4591
        have hw : |(1015549163/2000000000 : ℝ)|=(1015549163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s2_2 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343362277/10000000000 : ℝ)*x 0 + (5077745677/10000000000 : ℝ)*x 1 + (-1507316659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343362277/10000000000 : ℝ)^5615 ≤ (46462760392267/100000000000000 : ℝ)^4591 := by
    have hnat : (5343362277 : ℕ)^5615*100000000000000^4591 ≤ 46462760392267^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343362277 10000000000 46462760392267 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077745677/10000000000 : ℝ)^5615 ≤ (1746152967707/4000000000000 : ℝ)^4591 := by
    have hnat : (5077745677 : ℕ)^5615*4000000000000^4591 ≤ 1746152967707^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077745677 10000000000 1746152967707 4000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1507316659/10000000000 : ℝ)^5615 ≤ (1976683079457/20000000000000 : ℝ)^4591 := by
    have hnat : (1507316659 : ℕ)^5615*20000000000000^4591 ≤ 1976683079457^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507316659 10000000000 1976683079457 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343362277/10000000000 : ℝ), (5077745677/10000000000 : ℝ), (-1507316659/10000000000 : ℝ)] ![(46462760392267/100000000000000 : ℝ), (1746152967707/4000000000000 : ℝ), (1976683079457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343362277/10000000000 : ℝ)|^5615 ≤ (46462760392267/100000000000000 : ℝ)^4591
        have hw : |(5343362277/10000000000 : ℝ)|=(5343362277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077745677/10000000000 : ℝ)|^5615 ≤ (1746152967707/4000000000000 : ℝ)^4591
        have hw : |(5077745677/10000000000 : ℝ)|=(5077745677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1507316659/10000000000 : ℝ)|^5615 ≤ (1976683079457/20000000000000 : ℝ)^4591
        have hw : |(-1507316659/10000000000 : ℝ)|=(1507316659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s2_3 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (80846237/200000000 : ℝ)*x 0 + (67848601/200000000 : ℝ)*x 1 + (4757964201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80846237/200000000 : ℝ)^5615 ≤ (33028627504363/100000000000000 : ℝ)^4591 := by
    have hnat : (80846237 : ℕ)^5615*100000000000000^4591 ≤ 33028627504363^4591*200000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80846237 200000000 33028627504363 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67848601/200000000 : ℝ)^5615 ≤ (13327959625853/50000000000000 : ℝ)^4591 := by
    have hnat : (67848601 : ℕ)^5615*50000000000000^4591 ≤ 13327959625853^4591*200000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67848601 200000000 13327959625853 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4757964201/10000000000 : ℝ)^5615 ≤ (8063090645193/20000000000000 : ℝ)^4591 := by
    have hnat : (4757964201 : ℕ)^5615*20000000000000^4591 ≤ 8063090645193^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4757964201 10000000000 8063090645193 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80846237/200000000 : ℝ), (67848601/200000000 : ℝ), (4757964201/10000000000 : ℝ)] ![(33028627504363/100000000000000 : ℝ), (13327959625853/50000000000000 : ℝ), (8063090645193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80846237/200000000 : ℝ)|^5615 ≤ (33028627504363/100000000000000 : ℝ)^4591
        have hw : |(80846237/200000000 : ℝ)|=(80846237/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67848601/200000000 : ℝ)|^5615 ≤ (13327959625853/50000000000000 : ℝ)^4591
        have hw : |(67848601/200000000 : ℝ)|=(67848601/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4757964201/10000000000 : ℝ)|^5615 ≤ (8063090645193/20000000000000 : ℝ)^4591
        have hw : |(4757964201/10000000000 : ℝ)|=(4757964201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s2_4 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-640312803/5000000000 : ℝ)*x 0 + (2542340473/5000000000 : ℝ)*x 1 + (2751962339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640312803/5000000000 : ℝ)^5615 ≤ (323889653023/4000000000000 : ℝ)^4591 := by
    have hnat : (640312803 : ℕ)^5615*4000000000000^4591 ≤ 323889653023^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640312803 5000000000 323889653023 4000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542340473/5000000000 : ℝ)^5615 ≤ (21863378526949/50000000000000 : ℝ)^4591 := by
    have hnat : (2542340473 : ℕ)^5615*50000000000000^4591 ≤ 21863378526949^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542340473 5000000000 21863378526949 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751962339/5000000000 : ℝ)^5615 ≤ (24088000807699/50000000000000 : ℝ)^4591 := by
    have hnat : (2751962339 : ℕ)^5615*50000000000000^4591 ≤ 24088000807699^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751962339 5000000000 24088000807699 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-640312803/5000000000 : ℝ), (2542340473/5000000000 : ℝ), (2751962339/5000000000 : ℝ)] ![(323889653023/4000000000000 : ℝ), (21863378526949/50000000000000 : ℝ), (24088000807699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-640312803/5000000000 : ℝ)|^5615 ≤ (323889653023/4000000000000 : ℝ)^4591
        have hw : |(-640312803/5000000000 : ℝ)|=(640312803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542340473/5000000000 : ℝ)|^5615 ≤ (21863378526949/50000000000000 : ℝ)^4591
        have hw : |(2542340473/5000000000 : ℝ)|=(2542340473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751962339/5000000000 : ℝ)|^5615 ≤ (24088000807699/50000000000000 : ℝ)^4591
        have hw : |(2751962339/5000000000 : ℝ)|=(2751962339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s2_5 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307061479/2500000000 : ℝ)*x 0 + (-1081137459/10000000000 : ℝ)*x 1 + (5503924693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307061479/2500000000 : ℝ)^5615 ≤ (22620734472767/50000000000000 : ℝ)^4591 := by
    have hnat : (1307061479 : ℕ)^5615*50000000000000^4591 ≤ 22620734472767^4591*2500000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307061479 2500000000 22620734472767 50000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081137459/10000000000 : ℝ)^5615 ≤ (6582529261889/100000000000000 : ℝ)^4591 := by
    have hnat : (1081137459 : ℕ)^5615*100000000000000^4591 ≤ 6582529261889^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081137459 10000000000 6582529261889 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5503924693/10000000000 : ℝ)^5615 ≤ (48176001775979/100000000000000 : ℝ)^4591 := by
    have hnat : (5503924693 : ℕ)^5615*100000000000000^4591 ≤ 48176001775979^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503924693 10000000000 48176001775979 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307061479/2500000000 : ℝ), (-1081137459/10000000000 : ℝ), (5503924693/10000000000 : ℝ)] ![(22620734472767/50000000000000 : ℝ), (6582529261889/100000000000000 : ℝ), (48176001775979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307061479/2500000000 : ℝ)|^5615 ≤ (22620734472767/50000000000000 : ℝ)^4591
        have hw : |(1307061479/2500000000 : ℝ)|=(1307061479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081137459/10000000000 : ℝ)|^5615 ≤ (6582529261889/100000000000000 : ℝ)^4591
        have hw : |(-1081137459/10000000000 : ℝ)|=(1081137459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5503924693/10000000000 : ℝ)|^5615 ≤ (48176001775979/100000000000000 : ℝ)^4591
        have hw : |(5503924693/10000000000 : ℝ)|=(5503924693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s2_6 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5228245927/10000000000 : ℝ)*x 0 + (5503924683/10000000000 : ℝ)*x 1 + (-540568729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5228245927/10000000000 : ℝ)^5615 ≤ (45241469061951/100000000000000 : ℝ)^4591 := by
    have hnat : (5228245927 : ℕ)^5615*100000000000000^4591 ≤ 45241469061951^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228245927 10000000000 45241469061951 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503924683/10000000000 : ℝ)^5615 ≤ (1927040066757/4000000000000 : ℝ)^4591 := by
    have hnat : (5503924683 : ℕ)^5615*4000000000000^4591 ≤ 1927040066757^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503924683 10000000000 1927040066757 4000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540568729/5000000000 : ℝ)^5615 ≤ (6582529254443/100000000000000 : ℝ)^4591 := by
    have hnat : (540568729 : ℕ)^5615*100000000000000^4591 ≤ 6582529254443^4591*5000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540568729 5000000000 6582529254443 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5228245927/10000000000 : ℝ), (5503924683/10000000000 : ℝ), (-540568729/5000000000 : ℝ)] ![(45241469061951/100000000000000 : ℝ), (1927040066757/4000000000000 : ℝ), (6582529254443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5228245927/10000000000 : ℝ)|^5615 ≤ (45241469061951/100000000000000 : ℝ)^4591
        have hw : |(5228245927/10000000000 : ℝ)|=(5228245927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503924683/10000000000 : ℝ)|^5615 ≤ (1927040066757/4000000000000 : ℝ)^4591
        have hw : |(5503924683/10000000000 : ℝ)|=(5503924683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-540568729/5000000000 : ℝ)|^5615 ≤ (6582529254443/100000000000000 : ℝ)^4591
        have hw : |(-540568729/5000000000 : ℝ)|=(540568729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1740_s2_7 (p : ℝ) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4043488467/10000000000 : ℝ)*x 0 + (4736106839/10000000000 : ℝ)*x 1 + (3414748361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4043488467/10000000000 : ℝ)^5615 ≤ (6608077203429/20000000000000 : ℝ)^4591 := by
    have hnat : (4043488467 : ℕ)^5615*20000000000000^4591 ≤ 6608077203429^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043488467 10000000000 6608077203429 20000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4736106839/10000000000 : ℝ)^5615 ≤ (40089057736397/100000000000000 : ℝ)^4591 := by
    have hnat : (4736106839 : ℕ)^5615*100000000000000^4591 ≤ 40089057736397^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4736106839 10000000000 40089057736397 100000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3414748361/10000000000 : ℝ)^5615 ≤ (6717639056267/25000000000000 : ℝ)^4591 := by
    have hnat : (3414748361 : ℕ)^5615*25000000000000^4591 ≤ 6717639056267^4591*10000000000^5615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3414748361 10000000000 6717639056267 25000000000000 5615 4591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5615/1024 : ℝ)) 5615 4591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4043488467/10000000000 : ℝ), (4736106839/10000000000 : ℝ), (3414748361/10000000000 : ℝ)] ![(6608077203429/20000000000000 : ℝ), (40089057736397/100000000000000 : ℝ), (6717639056267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4043488467/10000000000 : ℝ)|^5615 ≤ (6608077203429/20000000000000 : ℝ)^4591
        have hw : |(4043488467/10000000000 : ℝ)|=(4043488467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4736106839/10000000000 : ℝ)|^5615 ≤ (40089057736397/100000000000000 : ℝ)^4591
        have hw : |(4736106839/10000000000 : ℝ)|=(4736106839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3414748361/10000000000 : ℝ)|^5615 ≤ (6717639056267/25000000000000 : ℝ)^4591
        have hw : |(3414748361/10000000000 : ℝ)|=(3414748361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1740_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4449/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9087/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18281/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8809/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18281/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8809/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18281/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8809/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18281/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8809/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18281/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8809/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18281/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8809/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8809/100000 : ℝ) ^ (5599/1024 : ℝ) ≤ (170254164382279/100000000000000000000 : ℝ) := by
    have hpowers : (8809/100000 : ℝ)^5599 ≤ (170254164382279/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8809 : ℕ)^5599*100000000000000000000^1024 ≤ 170254164382279^1024*100000^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8809 100000 170254164382279 100000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8809/100000 : ℝ)) (X := (170254164382279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18281/100000 : ℝ) ^ (5599/1024 : ℝ) ≤ (9221104045329897/100000000000000000000 : ℝ) := by
    have hpowers : (18281/100000 : ℝ)^5599 ≤ (9221104045329897/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18281 : ℕ)^5599*100000000000000000000^1024 ≤ 9221104045329897^1024*100000^5599 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18281 100000 9221104045329897 100000000000000000000 5599 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18281/100000 : ℝ)) (X := (9221104045329897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000170254164382279/50000000000000000000 : ℝ) ≤ (10000006227541411/10000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (50000170254164382279/50000000000000000000 : ℝ)^1024 ≤ (10000006227541411/10000000000000000 : ℝ)^5599 := by
      have hnat : (50000170254164382279 : ℕ)^1024*10000000000000000^5599 ≤ 10000006227541411^5599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000170254164382279 50000000000000000000 10000006227541411 10000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000006227541411/10000000000000000 : ℝ)) (X := (50000170254164382279/50000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6250586959888107011/6250000000000000000 : ℝ) ≤ (2000034350354863/2000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (6250586959888107011/6250000000000000000 : ℝ)^1024 ≤ (2000034350354863/2000000000000000 : ℝ)^5599 := by
      have hnat : (6250586959888107011 : ℕ)^1024*2000000000000000^5599 ≤ 2000034350354863^5599*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250586959888107011 6250000000000000000 2000034350354863 2000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000034350354863/2000000000000000 : ℝ)) (X := (6250586959888107011/6250000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009221104045329897/50000000000000000000 : ℝ) ≤ (10000337276007219/10000000000000000 : ℝ) ^ (5599/1024 : ℝ) := by
    have hpowers : (50009221104045329897/50000000000000000000 : ℝ)^1024 ≤ (10000337276007219/10000000000000000 : ℝ)^5599 := by
      have hnat : (50009221104045329897 : ℕ)^1024*10000000000000000^5599 ≤ 10000337276007219^5599*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009221104045329897 50000000000000000000 10000337276007219 10000000000000000 1024 5599 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000337276007219/10000000000000000 : ℝ)) (X := (50009221104045329897/50000000000000000000 : ℝ)) (by norm_num) 5599 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(170254164382279/100000000000000000000 : ℝ) ≤ ((1183964284766711779/1184000000000000000 : ℝ)+2*(20690529113/118400000000000 : ℝ)*(8809/100000 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (1183964284766711779/1184000000000000000 : ℝ)+2*(20690529113/118400000000000 : ℝ)*(8809/100000 : ℝ)=(10000006227541411/10000000000000000 : ℝ) by norm_num, show 1+2*(170254164382279/100000000000000000000 : ℝ)=(50000170254164382279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9221104045329897/100000000000000000000 : ℝ)+(170254164382279/100000000000000000000 : ℝ) ≤ ((1183964284766711779/1184000000000000000 : ℝ)+(20690529113/118400000000000 : ℝ)*((18281/100000 : ℝ)+(8809/100000 : ℝ)))^(5599/1024 : ℝ) := by
    rw [show (1183964284766711779/1184000000000000000 : ℝ)+(20690529113/118400000000000 : ℝ)*((18281/100000 : ℝ)+(8809/100000 : ℝ))=(2000034350354863/2000000000000000 : ℝ) by norm_num, show 1+(9221104045329897/100000000000000000000 : ℝ)+(170254164382279/100000000000000000000 : ℝ)=(6250586959888107011/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9221104045329897/100000000000000000000 : ℝ) ≤ ((1183964284766711779/1184000000000000000 : ℝ)+2*(20690529113/118400000000000 : ℝ)*(18281/100000 : ℝ))^(5599/1024 : ℝ) := by
    rw [show (1183964284766711779/1184000000000000000 : ℝ)+2*(20690529113/118400000000000 : ℝ)*(18281/100000 : ℝ)=(10000337276007219/10000000000000000 : ℝ) by norm_num, show 1+2*(9221104045329897/100000000000000000000 : ℝ)=(50009221104045329897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1183964284766711779/1184000000000000000 : ℝ)*(X 1 0+X 2 0)+(20690529113/118400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (8809/100000 : ℝ)) (hi := (18281/100000 : ℝ)) (c := (1183964284766711779/1184000000000000000 : ℝ)) (alpha := (20690529113/118400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1183964284766711779/1184000000000000000 : ℝ)*(X 0 1+X 2 1)+(20690529113/118400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (8809/100000 : ℝ)) (hi := (18281/100000 : ℝ)) (c := (1183964284766711779/1184000000000000000 : ℝ)) (alpha := (20690529113/118400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1183964284766711779/1184000000000000000 : ℝ)*(X 0 2+X 1 2)+(20690529113/118400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5599/1024 : ℝ)) (lo := (8809/100000 : ℝ)) (hi := (18281/100000 : ℝ)) (c := (1183964284766711779/1184000000000000000 : ℝ)) (alpha := (20690529113/118400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1280252253/10000000000 : ℝ)*X 0 0+(1377751461/2500000000 : ℝ)*X 0 1+(2538872969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5343362833/10000000000 : ℝ)*X 1 0+(-1507315741/10000000000 : ℝ)*X 1 1+(1015549163/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5343362277/10000000000 : ℝ)*X 2 0+(5077745677/10000000000 : ℝ)*X 2 1+(-1507316659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((80846237/200000000 : ℝ)*X 0 0+(67848601/200000000 : ℝ)*X 0 1+(4757964201/10000000000 : ℝ)*X 0 2+(80846237/200000000 : ℝ)*X 1 0+(67848601/200000000 : ℝ)*X 1 1+(4757964201/10000000000 : ℝ)*X 1 2+(80846237/200000000 : ℝ)*X 2 0+(67848601/200000000 : ℝ)*X 2 1+(4757964201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-640312803/5000000000 : ℝ)*X 0 0+(2542340473/5000000000 : ℝ)*X 0 1+(2751962339/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1307061479/2500000000 : ℝ)*X 1 0+(-1081137459/10000000000 : ℝ)*X 1 1+(5503924693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5228245927/10000000000 : ℝ)*X 2 0+(5503924683/10000000000 : ℝ)*X 2 1+(-540568729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4043488467/10000000000 : ℝ)*X 0 0+(4736106839/10000000000 : ℝ)*X 0 1+(3414748361/10000000000 : ℝ)*X 0 2+(4043488467/10000000000 : ℝ)*X 1 0+(4736106839/10000000000 : ℝ)*X 1 1+(3414748361/10000000000 : ℝ)*X 1 2+(4043488467/10000000000 : ℝ)*X 2 0+(4736106839/10000000000 : ℝ)*X 2 1+(3414748361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1740_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6224918270816750294733/2960000000000000000000000000 : ℝ) := by norm_num
    linear_combination (310912279/50000000000000 : ℝ)*(base19) + (65294307/20000000000000 : ℝ)*(base23) + (119020419/100000000000000 : ℝ)*(upper3) + (16133177/100000000000000 : ℝ)*(lower4) + (760102667048393/50000000000000 : ℝ)*(major0) + (760102667048393/50000000000000 : ℝ)*(major1) + (760102667048393/50000000000000 : ℝ)*(major2) + (1154044782195729/50000000000000 : ℝ)*(sp0) + (144255791600193/6250000000000 : ℝ)*(sp1) + (144255562369891/6250000000000 : ℝ)*(sp2) + (366157797049267/50000000000000 : ℝ)*(sp3) + (3723036189/100000000000000 : ℝ)*(sp4) + (792607571/20000000000000 : ℝ)*(sp6) + (343313391/20000000000000 : ℝ)*(sp7) + (732317310665489/100000000000000 : ℝ)*(f.failure) + (1154046643713823/50000000000000 : ℝ)*(f.sum) + (1797974953489/2960000000000000000000000000 : ℝ)*base65 + (110617653896988853/59200000000000000000000000000000 : ℝ)*base68 + (50972146901788853/59200000000000000000000000000000 : ℝ)*base70 + (108064766258588853/59200000000000000000000000000000 : ℝ)*base72 + (2615768903889/2960000000000000000000000000 : ℝ)*base73 + (451191440237411147/59200000000000000000000000000000 : ℝ)*base75 + (90766295915811147/59200000000000000000000000000000 : ℝ)*base77 + (162719465387811147/59200000000000000000000000000000 : ℝ)*base79 + (22328307791/2960000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (32266359/5000000000000000000000 : ℝ)*base90 + (32266359/5000000000000000000000 : ℝ)*base92 + (32266359/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119186473973176834162674279/14800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26860219/2500000000000 : ℝ)*(base19) + (1156272709/100000000000000 : ℝ)*(base23) + (178110377/100000000000000 : ℝ)*(upper3) + (8448853/25000000000000 : ℝ)*(lower4) + (169887691/100000000000000 : ℝ)*(upper5) + (785511003815833/50000000000000 : ℝ)*(major0) + (785511003815833/50000000000000 : ℝ)*(major1) + (785511003815833/50000000000000 : ℝ)*(major2) + (1447888573/20000000000000 : ℝ)*(sp1) + (779381361/10000000000000 : ℝ)*(sp2) + (2385246894570703/100000000000000 : ℝ)*(sp4) + (1192619290359539/50000000000000 : ℝ)*(sp5) + (74538685765137/3125000000000 : ℝ)*(sp6) + (189199213063653/25000000000000 : ℝ)*(sp7) + (189199213063653/25000000000000 : ℝ)*(f.failure) + (2385246894570703/100000000000000 : ℝ)*(f.sum) + (9167025960431/2960000000000000000000000000 : ℝ)*base66 + (694303236413886907/59200000000000000000000000000000 : ℝ)*base67 + (358875600738113093/59200000000000000000000000000000 : ℝ)*base70 + (441420651186686907/59200000000000000000000000000000 : ℝ)*base71 + (15502289171169/2960000000000000000000000000 : ℝ)*base73 + (154492331077886907/59200000000000000000000000000000 : ℝ)*base75 + (557365512042686907/59200000000000000000000000000000 : ℝ)*base77 + (343070275537086907/59200000000000000000000000000000 : ℝ)*base79 + (9223169121071/2960000000000000000000000000 : ℝ)*base82 + (17760643/1250000000000000000000 : ℝ)*base90 + (17760643/1250000000000000000000 : ℝ)*base92 + (17760643/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1740_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8809/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4449/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9087/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1740_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1740_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4449/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9087/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1740_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1740_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1740_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5599/1024 : ℝ) ≤ p) (hpb : p ≤ (5615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (103794169/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4449/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9087/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1740_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
