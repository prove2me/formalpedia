-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1756_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:24:19.797002+00:00
-- url     : https://prove2.me/submissions/f7c0b3f5-d528-4959-b910-2a88258b2791

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
theorem support_rectangle_w1756_s3_0 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066419897/2000000000 : ℝ)*x 0 + (-140182323/1000000000 : ℝ)*x 1 + (1985457/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066419897/2000000000 : ℝ)^5871 ≤ (23343796444663/50000000000000 : ℝ)^4847 := by
    have hnat : (1066419897 : ℕ)^5871*50000000000000^4847 ≤ 23343796444663^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066419897 2000000000 23343796444663 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140182323/1000000000 : ℝ)^5871 ≤ (4627960707187/50000000000000 : ℝ)^4847 := by
    have hnat : (140182323 : ℕ)^5871*50000000000000^4847 ≤ 4627960707187^4847*1000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140182323 1000000000 4627960707187 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985457/3906250 : ℝ)^5871 ≤ (11014121418411/25000000000000 : ℝ)^4847 := by
    have hnat : (1985457 : ℕ)^5871*25000000000000^4847 ≤ 11014121418411^4847*3906250^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985457 3906250 11014121418411 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066419897/2000000000 : ℝ), (-140182323/1000000000 : ℝ), (1985457/3906250 : ℝ)] ![(23343796444663/50000000000000 : ℝ), (4627960707187/50000000000000 : ℝ), (11014121418411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066419897/2000000000 : ℝ)|^5871 ≤ (23343796444663/50000000000000 : ℝ)^4847
        have hw : |(1066419897/2000000000 : ℝ)|=(1066419897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140182323/1000000000 : ℝ)|^5871 ≤ (4627960707187/50000000000000 : ℝ)^4847
        have hw : |(-140182323/1000000000 : ℝ)|=(140182323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1985457/3906250 : ℝ)|^5871 ≤ (11014121418411/25000000000000 : ℝ)^4847
        have hw : |(1985457/3906250 : ℝ)|=(1985457/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s3_1 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-594928193/5000000000 : ℝ)*x 0 + (50894421/100000000 : ℝ)*x 1 + (5482230303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (594928193/5000000000 : ℝ)^5871 ≤ (3794453044519/50000000000000 : ℝ)^4847 := by
    have hnat : (594928193 : ℕ)^5871*50000000000000^4847 ≤ 3794453044519^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594928193 5000000000 3794453044519 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50894421/100000000 : ℝ)^5871 ≤ (8825309337279/20000000000000 : ℝ)^4847 := by
    have hnat : (50894421 : ℕ)^5871*20000000000000^4847 ≤ 8825309337279^4847*100000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50894421 100000000 8825309337279 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5482230303/10000000000 : ℝ)^5871 ≤ (24142273602777/50000000000000 : ℝ)^4847 := by
    have hnat : (5482230303 : ℕ)^5871*50000000000000^4847 ≤ 24142273602777^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482230303 10000000000 24142273602777 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-594928193/5000000000 : ℝ), (50894421/100000000 : ℝ), (5482230303/10000000000 : ℝ)] ![(3794453044519/50000000000000 : ℝ), (8825309337279/20000000000000 : ℝ), (24142273602777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-594928193/5000000000 : ℝ)|^5871 ≤ (3794453044519/50000000000000 : ℝ)^4847
        have hw : |(-594928193/5000000000 : ℝ)|=(594928193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50894421/100000000 : ℝ)|^5871 ≤ (8825309337279/20000000000000 : ℝ)^4847
        have hw : |(50894421/100000000 : ℝ)|=(50894421/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5482230303/10000000000 : ℝ)|^5871 ≤ (24142273602777/50000000000000 : ℝ)^4847
        have hw : |(5482230303/10000000000 : ℝ)|=(5482230303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s3_2 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224591809/10000000000 : ℝ)*x 0 + (-1002362879/10000000000 : ℝ)*x 1 + (2741115131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224591809/10000000000 : ℝ)^5871 ≤ (45549832342367/100000000000000 : ℝ)^4847 := by
    have hnat : (5224591809 : ℕ)^5871*100000000000000^4847 ≤ 45549832342367^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224591809 10000000000 45549832342367 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002362879/10000000000 : ℝ)^5871 ≤ (1541405217523/25000000000000 : ℝ)^4847 := by
    have hnat : (1002362879 : ℕ)^5871*25000000000000^4847 ≤ 1541405217523^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002362879 10000000000 1541405217523 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741115131/5000000000 : ℝ)^5871 ≤ (48284546768159/100000000000000 : ℝ)^4847 := by
    have hnat : (2741115131 : ℕ)^5871*100000000000000^4847 ≤ 48284546768159^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741115131 5000000000 48284546768159 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224591809/10000000000 : ℝ), (-1002362879/10000000000 : ℝ), (2741115131/5000000000 : ℝ)] ![(45549832342367/100000000000000 : ℝ), (1541405217523/25000000000000 : ℝ), (48284546768159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224591809/10000000000 : ℝ)|^5871 ≤ (45549832342367/100000000000000 : ℝ)^4847
        have hw : |(5224591809/10000000000 : ℝ)|=(5224591809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002362879/10000000000 : ℝ)|^5871 ≤ (1541405217523/25000000000000 : ℝ)^4847
        have hw : |(-1002362879/10000000000 : ℝ)|=(1002362879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741115131/5000000000 : ℝ)|^5871 ≤ (48284546768159/100000000000000 : ℝ)^4847
        have hw : |(2741115131/5000000000 : ℝ)|=(2741115131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s3_3 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224591717/10000000000 : ℝ)*x 0 + (2741115139/5000000000 : ℝ)*x 1 + (-250590747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224591717/10000000000 : ℝ)^5871 ≤ (22774915685413/50000000000000 : ℝ)^4847 := by
    have hnat : (5224591717 : ℕ)^5871*50000000000000^4847 ≤ 22774915685413^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224591717 10000000000 22774915685413 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2741115139/5000000000 : ℝ)^5871 ≤ (965690938777/2000000000000 : ℝ)^4847 := by
    have hnat : (2741115139 : ℕ)^5871*2000000000000^4847 ≤ 965690938777^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741115139 5000000000 965690938777 2000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250590747/2500000000 : ℝ)^5871 ≤ (6165621682207/100000000000000 : ℝ)^4847 := by
    have hnat : (250590747 : ℕ)^5871*100000000000000^4847 ≤ 6165621682207^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250590747 2500000000 6165621682207 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224591717/10000000000 : ℝ), (2741115139/5000000000 : ℝ), (-250590747/2500000000 : ℝ)] ![(22774915685413/50000000000000 : ℝ), (965690938777/2000000000000 : ℝ), (6165621682207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224591717/10000000000 : ℝ)|^5871 ≤ (22774915685413/50000000000000 : ℝ)^4847
        have hw : |(5224591717/10000000000 : ℝ)|=(5224591717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2741115139/5000000000 : ℝ)|^5871 ≤ (965690938777/2000000000000 : ℝ)^4847
        have hw : |(2741115139/5000000000 : ℝ)|=(2741115139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250590747/2500000000 : ℝ)|^5871 ≤ (6165621682207/100000000000000 : ℝ)^4847
        have hw : |(-250590747/2500000000 : ℝ)|=(250590747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s3_4 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1002431963/2500000000 : ℝ)*x 0 + (1175194379/2500000000 : ℝ)*x 1 + (3378599179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002431963/2500000000 : ℝ)^5871 ≤ (6611455524619/20000000000000 : ℝ)^4847 := by
    have hnat : (1002431963 : ℕ)^5871*20000000000000^4847 ≤ 6611455524619^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002431963 2500000000 6611455524619 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1175194379/2500000000 : ℝ)^5871 ≤ (40078432380467/100000000000000 : ℝ)^4847 := by
    have hnat : (1175194379 : ℕ)^5871*100000000000000^4847 ≤ 40078432380467^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175194379 2500000000 40078432380467 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3378599179/10000000000 : ℝ)^5871 ≤ (6716072495051/25000000000000 : ℝ)^4847 := by
    have hnat : (3378599179 : ℕ)^5871*25000000000000^4847 ≤ 6716072495051^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3378599179 10000000000 6716072495051 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1002431963/2500000000 : ℝ), (1175194379/2500000000 : ℝ), (3378599179/10000000000 : ℝ)] ![(6611455524619/20000000000000 : ℝ), (40078432380467/100000000000000 : ℝ), (6716072495051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1002431963/2500000000 : ℝ)|^5871 ≤ (6611455524619/20000000000000 : ℝ)^4847
        have hw : |(1002431963/2500000000 : ℝ)|=(1002431963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1175194379/2500000000 : ℝ)|^5871 ≤ (40078432380467/100000000000000 : ℝ)^4847
        have hw : |(1175194379/2500000000 : ℝ)|=(1175194379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3378599179/10000000000 : ℝ)|^5871 ≤ (6716072495051/25000000000000 : ℝ)^4847
        have hw : |(3378599179/10000000000 : ℝ)|=(3378599179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1756_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (893/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1139/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17859/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (893/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1139/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (893/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1139/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (893/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1139/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (893/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1139/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (893/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1139/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (893/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1139/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1139/12500 : ℝ) ^ (5855/1024 : ℝ) ≤ (28135000103967/25000000000000000000 : ℝ) := by
    have hpowers : (1139/12500 : ℝ)^5855 ≤ (28135000103967/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1139 : ℕ)^5855*25000000000000000000^1024 ≤ 28135000103967^1024*12500^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1139 12500 28135000103967 25000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1139/12500 : ℝ)) (X := (28135000103967/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (893/5000 : ℝ) ^ (5855/1024 : ℝ) ≤ (1319373209904703/25000000000000000000 : ℝ) := by
    have hpowers : (893/5000 : ℝ)^5855 ≤ (1319373209904703/25000000000000000000 : ℝ)^1024 := by
      have hnat : (893 : ℕ)^5855*25000000000000000000^1024 ≤ 1319373209904703^1024*5000^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        893 5000 1319373209904703 25000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (893/5000 : ℝ)) (X := (1319373209904703/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500028135000103967/12500000000000000000 : ℝ) ≤ (625000246030857/625000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (12500028135000103967/12500000000000000000 : ℝ)^1024 ≤ (625000246030857/625000000000000 : ℝ)^5855 := by
      have hnat : (12500028135000103967 : ℕ)^1024*625000000000000^5855 ≤ 625000246030857^5855*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500028135000103967 12500000000000000000 625000246030857 625000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000246030857/625000000000000 : ℝ)) (X := (12500028135000103967/12500000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500134750821000867/2500000000000000000 : ℝ) ≤ (1000009426594191/1000000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (2500134750821000867/2500000000000000000 : ℝ)^1024 ≤ (1000009426594191/1000000000000000 : ℝ)^5855 := by
      have hnat : (2500134750821000867 : ℕ)^1024*1000000000000000^5855 ≤ 1000009426594191^5855*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500134750821000867 2500000000000000000 1000009426594191 1000000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000009426594191/1000000000000000 : ℝ)) (X := (2500134750821000867/2500000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12501319373209904703/12500000000000000000 : ℝ) ≤ (2500046148847527/2500000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (12501319373209904703/12500000000000000000 : ℝ)^1024 ≤ (2500046148847527/2500000000000000 : ℝ)^5855 := by
      have hnat : (12501319373209904703 : ℕ)^1024*2500000000000000^5855 ≤ 2500046148847527^5855*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501319373209904703 12500000000000000000 2500046148847527 2500000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500046148847527/2500000000000000 : ℝ)) (X := (12501319373209904703/12500000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28135000103967/25000000000000000000 : ℝ) ≤ ((911233211172739919/911250000000000000 : ℝ)+2*(15054908033/145800000000000 : ℝ)*(1139/12500 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (911233211172739919/911250000000000000 : ℝ)+2*(15054908033/145800000000000 : ℝ)*(1139/12500 : ℝ)=(625000246030857/625000000000000 : ℝ) by norm_num, show 1+2*(28135000103967/25000000000000000000 : ℝ)=(12500028135000103967/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1319373209904703/25000000000000000000 : ℝ)+(28135000103967/25000000000000000000 : ℝ) ≤ ((911233211172739919/911250000000000000 : ℝ)+(15054908033/145800000000000 : ℝ)*((893/5000 : ℝ)+(1139/12500 : ℝ)))^(5855/1024 : ℝ) := by
    rw [show (911233211172739919/911250000000000000 : ℝ)+(15054908033/145800000000000 : ℝ)*((893/5000 : ℝ)+(1139/12500 : ℝ))=(1000009426594191/1000000000000000 : ℝ) by norm_num, show 1+(1319373209904703/25000000000000000000 : ℝ)+(28135000103967/25000000000000000000 : ℝ)=(2500134750821000867/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1319373209904703/25000000000000000000 : ℝ) ≤ ((911233211172739919/911250000000000000 : ℝ)+2*(15054908033/145800000000000 : ℝ)*(893/5000 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (911233211172739919/911250000000000000 : ℝ)+2*(15054908033/145800000000000 : ℝ)*(893/5000 : ℝ)=(2500046148847527/2500000000000000 : ℝ) by norm_num, show 1+2*(1319373209904703/25000000000000000000 : ℝ)=(12501319373209904703/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (911233211172739919/911250000000000000 : ℝ)*(X 1 0+X 2 0)+(15054908033/145800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (1139/12500 : ℝ)) (hi := (893/5000 : ℝ)) (c := (911233211172739919/911250000000000000 : ℝ)) (alpha := (15054908033/145800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (911233211172739919/911250000000000000 : ℝ)*(X 0 1+X 2 1)+(15054908033/145800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (1139/12500 : ℝ)) (hi := (893/5000 : ℝ)) (c := (911233211172739919/911250000000000000 : ℝ)) (alpha := (15054908033/145800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (911233211172739919/911250000000000000 : ℝ)*(X 0 2+X 1 2)+(15054908033/145800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (1139/12500 : ℝ)) (hi := (893/5000 : ℝ)) (c := (911233211172739919/911250000000000000 : ℝ)) (alpha := (15054908033/145800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1066419897/2000000000 : ℝ)*X 1 0+(-140182323/1000000000 : ℝ)*X 1 1+(1985457/3906250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s3_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-594928193/5000000000 : ℝ)*X 0 0+(50894421/100000000 : ℝ)*X 0 1+(5482230303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s3_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5224591809/10000000000 : ℝ)*X 1 0+(-1002362879/10000000000 : ℝ)*X 1 1+(2741115131/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s3_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5224591717/10000000000 : ℝ)*X 2 0+(2741115139/5000000000 : ℝ)*X 2 1+(-250590747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s3_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1002431963/2500000000 : ℝ)*X 0 0+(1175194379/2500000000 : ℝ)*X 0 1+(3378599179/10000000000 : ℝ)*X 0 2+(1002431963/2500000000 : ℝ)*X 1 0+(1175194379/2500000000 : ℝ)*X 1 1+(3378599179/10000000000 : ℝ)*X 1 2+(1002431963/2500000000 : ℝ)*X 2 0+(1175194379/2500000000 : ℝ)*X 2 1+(3378599179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s3_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25735221119565591895721869/2531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1260885677/100000000000000 : ℝ)*(base19) + (663339303/50000000000000 : ℝ)*(base23) + (359803223/100000000000000 : ℝ)*(lower1) + (48489203/25000000000000 : ℝ)*(upper3) + (370379/625000000000 : ℝ)*(lower4) + (216021347/100000000000000 : ℝ)*(upper5) + (825554166717847/50000000000000 : ℝ)*(major0) + (825554166717847/50000000000000 : ℝ)*(major1) + (825554166717847/50000000000000 : ℝ)*(major2) + (27241379/20000000000000 : ℝ)*(sp0) + (318236463886471/12500000000000 : ℝ)*(sp1) + (636472578499799/25000000000000 : ℝ)*(sp2) + (1272945192206581/50000000000000 : ℝ)*(sp3) + (756324616879583/100000000000000 : ℝ)*(sp4) + (756324616879583/100000000000000 : ℝ)*(f.failure) + (318236463886471/12500000000000 : ℝ)*(f.sum) + (22307321113091/3645000000000000000000000000 : ℝ)*base65 + (120930937054328143/45562500000000000000000000000000 : ℝ)*base67 + (207056160861734357/45562500000000000000000000000000 : ℝ)*base70 + (139908095242890643/45562500000000000000000000000000 : ℝ)*base71 + (7202352080321/3645000000000000000000000000 : ℝ)*base73 + (175029959576265643/45562500000000000000000000000000 : ℝ)*base75 + (142011054528203143/45562500000000000000000000000000 : ℝ)*base77 + (104853404573421857/45562500000000000000000000000000 : ℝ)*base80 + (1382221681097/1822500000000000000000000000 : ℝ)*base82 + (11830039/2000000000000000000000 : ℝ)*base90 + (11830039/2000000000000000000000 : ℝ)*base92 + (11830039/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1756_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (893/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17859/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1756_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1756_box_0 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-812496019/10000000000 : ℝ)*x 0 + (84670047/156250000 : ℝ)*x 1 + (1083776641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (812496019/10000000000 : ℝ)^5871 ≤ (4780848192251/100000000000000 : ℝ)^4847 := by
    have hnat : (812496019 : ℕ)^5871*100000000000000^4847 ≤ 4780848192251^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812496019 10000000000 4780848192251 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84670047/156250000 : ℝ)^5871 ≤ (47609574851397/100000000000000 : ℝ)^4847 := by
    have hnat : (84670047 : ℕ)^5871*100000000000000^4847 ≤ 47609574851397^4847*156250000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84670047 156250000 47609574851397 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083776641/2000000000 : ℝ)^5871 ≤ (47609576947873/100000000000000 : ℝ)^4847 := by
    have hnat : (1083776641 : ℕ)^5871*100000000000000^4847 ≤ 47609576947873^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083776641 2000000000 47609576947873 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-812496019/10000000000 : ℝ), (84670047/156250000 : ℝ), (1083776641/2000000000 : ℝ)] ![(4780848192251/100000000000000 : ℝ), (47609574851397/100000000000000 : ℝ), (47609576947873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-812496019/10000000000 : ℝ)|^5871 ≤ (4780848192251/100000000000000 : ℝ)^4847
        have hw : |(-812496019/10000000000 : ℝ)|=(812496019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84670047/156250000 : ℝ)|^5871 ≤ (47609574851397/100000000000000 : ℝ)^4847
        have hw : |(84670047/156250000 : ℝ)|=(84670047/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083776641/2000000000 : ℝ)|^5871 ≤ (47609576947873/100000000000000 : ℝ)^4847
        have hw : |(1083776641/2000000000 : ℝ)|=(1083776641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_1 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298442181/2500000000 : ℝ)*x 0 + (-7092673/62500000 : ℝ)*x 1 + (5418883127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298442181/2500000000 : ℝ)^5871 ≤ (11306134140739/25000000000000 : ℝ)^4847 := by
    have hnat : (1298442181 : ℕ)^5871*25000000000000^4847 ≤ 11306134140739^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298442181 2500000000 11306134140739 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7092673/62500000 : ℝ)^5871 ≤ (7165887299809/100000000000000 : ℝ)^4847 := by
    have hnat : (7092673 : ℕ)^5871*100000000000000^4847 ≤ 7165887299809^4847*62500000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7092673 62500000 7165887299809 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418883127/10000000000 : ℝ)^5871 ≤ (11902394029449/25000000000000 : ℝ)^4847 := by
    have hnat : (5418883127 : ℕ)^5871*25000000000000^4847 ≤ 11902394029449^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418883127 10000000000 11902394029449 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298442181/2500000000 : ℝ), (-7092673/62500000 : ℝ), (5418883127/10000000000 : ℝ)] ![(11306134140739/25000000000000 : ℝ), (7165887299809/100000000000000 : ℝ), (11902394029449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298442181/2500000000 : ℝ)|^5871 ≤ (11306134140739/25000000000000 : ℝ)^4847
        have hw : |(1298442181/2500000000 : ℝ)|=(1298442181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7092673/62500000 : ℝ)|^5871 ≤ (7165887299809/100000000000000 : ℝ)^4847
        have hw : |(-7092673/62500000 : ℝ)|=(7092673/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418883127/10000000000 : ℝ)|^5871 ≤ (11902394029449/25000000000000 : ℝ)^4847
        have hw : |(5418883127/10000000000 : ℝ)|=(5418883127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_2 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519376879/1000000000 : ℝ)*x 0 + (2709441559/5000000000 : ℝ)*x 1 + (-567413801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519376879/1000000000 : ℝ)^5871 ≤ (45224537259061/100000000000000 : ℝ)^4847 := by
    have hnat : (519376879 : ℕ)^5871*100000000000000^4847 ≤ 45224537259061^4847*1000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519376879 1000000000 45224537259061 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709441559/5000000000 : ℝ)^5871 ≤ (23804788011009/50000000000000 : ℝ)^4847 := by
    have hnat : (2709441559 : ℕ)^5871*50000000000000^4847 ≤ 23804788011009^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709441559 5000000000 23804788011009 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567413801/5000000000 : ℝ)^5871 ≤ (7165886703223/100000000000000 : ℝ)^4847 := by
    have hnat : (567413801 : ℕ)^5871*100000000000000^4847 ≤ 7165886703223^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567413801 5000000000 7165886703223 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519376879/1000000000 : ℝ), (2709441559/5000000000 : ℝ), (-567413801/5000000000 : ℝ)] ![(45224537259061/100000000000000 : ℝ), (23804788011009/50000000000000 : ℝ), (7165886703223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519376879/1000000000 : ℝ)|^5871 ≤ (45224537259061/100000000000000 : ℝ)^4847
        have hw : |(519376879/1000000000 : ℝ)|=(519376879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709441559/5000000000 : ℝ)|^5871 ≤ (23804788011009/50000000000000 : ℝ)^4847
        have hw : |(2709441559/5000000000 : ℝ)|=(2709441559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567413801/5000000000 : ℝ)|^5871 ≤ (7165886703223/100000000000000 : ℝ)^4847
        have hw : |(-567413801/5000000000 : ℝ)|=(567413801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_3 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1133494941/2500000000 : ℝ)*x 0 + (756841097/2000000000 : ℝ)*x 1 + (3784205723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1133494941/2500000000 : ℝ)^5871 ≤ (19181203054151/50000000000000 : ℝ)^4847 := by
    have hnat : (1133494941 : ℕ)^5871*50000000000000^4847 ≤ 19181203054151^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133494941 2500000000 19181203054151 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (756841097/2000000000 : ℝ)^5871 ≤ (30818795768553/100000000000000 : ℝ)^4847 := by
    have hnat : (756841097 : ℕ)^5871*100000000000000^4847 ≤ 30818795768553^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756841097 2000000000 30818795768553 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3784205723/10000000000 : ℝ)^5871 ≤ (3081879811633/10000000000000 : ℝ)^4847 := by
    have hnat : (3784205723 : ℕ)^5871*10000000000000^4847 ≤ 3081879811633^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3784205723 10000000000 3081879811633 10000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1133494941/2500000000 : ℝ), (756841097/2000000000 : ℝ), (3784205723/10000000000 : ℝ)] ![(19181203054151/50000000000000 : ℝ), (30818795768553/100000000000000 : ℝ), (3081879811633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1133494941/2500000000 : ℝ)|^5871 ≤ (19181203054151/50000000000000 : ℝ)^4847
        have hw : |(1133494941/2500000000 : ℝ)|=(1133494941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(756841097/2000000000 : ℝ)|^5871 ≤ (30818795768553/100000000000000 : ℝ)^4847
        have hw : |(756841097/2000000000 : ℝ)|=(756841097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3784205723/10000000000 : ℝ)|^5871 ≤ (3081879811633/10000000000000 : ℝ)^4847
        have hw : |(3784205723/10000000000 : ℝ)|=(3784205723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_4 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-802933243/5000000000 : ℝ)*x 0 + (5129160523/10000000000 : ℝ)*x 1 + (2564579917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (802933243/5000000000 : ℝ)^5871 ≤ (1091198792479/10000000000000 : ℝ)^4847 := by
    have hnat : (802933243 : ℕ)^5871*10000000000000^4847 ≤ 1091198792479^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802933243 5000000000 1091198792479 10000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129160523/10000000000 : ℝ)^5871 ≤ (11136002414019/25000000000000 : ℝ)^4847 := by
    have hnat : (5129160523 : ℕ)^5871*25000000000000^4847 ≤ 11136002414019^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129160523 10000000000 11136002414019 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564579917/5000000000 : ℝ)^5871 ≤ (22272001204179/50000000000000 : ℝ)^4847 := by
    have hnat : (2564579917 : ℕ)^5871*50000000000000^4847 ≤ 22272001204179^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564579917 5000000000 22272001204179 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-802933243/5000000000 : ℝ), (5129160523/10000000000 : ℝ), (2564579917/5000000000 : ℝ)] ![(1091198792479/10000000000000 : ℝ), (11136002414019/25000000000000 : ℝ), (22272001204179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-802933243/5000000000 : ℝ)|^5871 ≤ (1091198792479/10000000000000 : ℝ)^4847
        have hw : |(-802933243/5000000000 : ℝ)|=(802933243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129160523/10000000000 : ℝ)|^5871 ≤ (11136002414019/25000000000000 : ℝ)^4847
        have hw : |(5129160523/10000000000 : ℝ)|=(5129160523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564579917/5000000000 : ℝ)|^5871 ≤ (22272001204179/50000000000000 : ℝ)^4847
        have hw : |(2564579917/5000000000 : ℝ)|=(2564579917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_5 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387227369/10000000000 : ℝ)*x 0 + (-253251839/2000000000 : ℝ)*x 1 + (1025832047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387227369/10000000000 : ℝ)^5871 ≤ (47272903481887/100000000000000 : ℝ)^4847 := by
    have hnat : (5387227369 : ℕ)^5871*100000000000000^4847 ≤ 47272903481887^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387227369 10000000000 47272903481887 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253251839/2000000000 : ℝ)^5871 ≤ (2045772468771/25000000000000 : ℝ)^4847 := by
    have hnat : (253251839 : ℕ)^5871*25000000000000^4847 ≤ 2045772468771^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253251839 2000000000 2045772468771 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025832047/2000000000 : ℝ)^5871 ≤ (44544006626551/100000000000000 : ℝ)^4847 := by
    have hnat : (1025832047 : ℕ)^5871*100000000000000^4847 ≤ 44544006626551^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025832047 2000000000 44544006626551 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387227369/10000000000 : ℝ), (-253251839/2000000000 : ℝ), (1025832047/2000000000 : ℝ)] ![(47272903481887/100000000000000 : ℝ), (2045772468771/25000000000000 : ℝ), (44544006626551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387227369/10000000000 : ℝ)|^5871 ≤ (47272903481887/100000000000000 : ℝ)^4847
        have hw : |(5387227369/10000000000 : ℝ)|=(5387227369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253251839/2000000000 : ℝ)|^5871 ≤ (2045772468771/25000000000000 : ℝ)^4847
        have hw : |(-253251839/2000000000 : ℝ)|=(253251839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025832047/2000000000 : ℝ)|^5871 ≤ (44544006626551/100000000000000 : ℝ)^4847
        have hw : |(1025832047/2000000000 : ℝ)|=(1025832047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_6 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387227223/10000000000 : ℝ)*x 0 + (2564580117/5000000000 : ℝ)*x 1 + (-253251879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387227223/10000000000 : ℝ)^5871 ≤ (11818225482519/25000000000000 : ℝ)^4847 := by
    have hnat : (5387227223 : ℕ)^5871*25000000000000^4847 ≤ 11818225482519^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387227223 10000000000 11818225482519 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564580117/5000000000 : ℝ)^5871 ≤ (1392000206751/3125000000000 : ℝ)^4847 := by
    have hnat : (2564580117 : ℕ)^5871*3125000000000^4847 ≤ 1392000206751^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564580117 5000000000 1392000206751 3125000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253251879/2000000000 : ℝ)^5871 ≤ (8183091440623/100000000000000 : ℝ)^4847 := by
    have hnat : (253251879 : ℕ)^5871*100000000000000^4847 ≤ 8183091440623^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253251879 2000000000 8183091440623 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387227223/10000000000 : ℝ), (2564580117/5000000000 : ℝ), (-253251879/2000000000 : ℝ)] ![(11818225482519/25000000000000 : ℝ), (1392000206751/3125000000000 : ℝ), (8183091440623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387227223/10000000000 : ℝ)|^5871 ≤ (11818225482519/25000000000000 : ℝ)^4847
        have hw : |(5387227223/10000000000 : ℝ)|=(5387227223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564580117/5000000000 : ℝ)|^5871 ≤ (1392000206751/3125000000000 : ℝ)^4847
        have hw : |(2564580117/5000000000 : ℝ)|=(2564580117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253251879/2000000000 : ℝ)|^5871 ≤ (8183091440623/100000000000000 : ℝ)^4847
        have hw : |(-253251879/2000000000 : ℝ)|=(253251879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_7 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3445540341/10000000000 : ℝ)*x 0 + (865268417/2000000000 : ℝ)*x 1 + (2163170681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3445540341/10000000000 : ℝ)^5871 ≤ (5502070430707/20000000000000 : ℝ)^4847 := by
    have hnat : (3445540341 : ℕ)^5871*20000000000000^4847 ≤ 5502070430707^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3445540341 10000000000 5502070430707 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (865268417/2000000000 : ℝ)^5871 ≤ (4530603448017/12500000000000 : ℝ)^4847 := by
    have hnat : (865268417 : ℕ)^5871*12500000000000^4847 ≤ 4530603448017^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865268417 2000000000 4530603448017 12500000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163170681/5000000000 : ℝ)^5871 ≤ (18122410123703/50000000000000 : ℝ)^4847 := by
    have hnat : (2163170681 : ℕ)^5871*50000000000000^4847 ≤ 18122410123703^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163170681 5000000000 18122410123703 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3445540341/10000000000 : ℝ), (865268417/2000000000 : ℝ), (2163170681/5000000000 : ℝ)] ![(5502070430707/20000000000000 : ℝ), (4530603448017/12500000000000 : ℝ), (18122410123703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3445540341/10000000000 : ℝ)|^5871 ≤ (5502070430707/20000000000000 : ℝ)^4847
        have hw : |(3445540341/10000000000 : ℝ)|=(3445540341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(865268417/2000000000 : ℝ)|^5871 ≤ (4530603448017/12500000000000 : ℝ)^4847
        have hw : |(865268417/2000000000 : ℝ)|=(865268417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2163170681/5000000000 : ℝ)|^5871 ≤ (18122410123703/50000000000000 : ℝ)^4847
        have hw : |(2163170681/5000000000 : ℝ)|=(2163170681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_8 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-358293859/2500000000 : ℝ)*x 0 + (4907952913/10000000000 : ℝ)*x 1 + (342524489/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358293859/2500000000 : ℝ)^5871 ≤ (1901451219313/20000000000000 : ℝ)^4847 := by
    have hnat : (358293859 : ℕ)^5871*20000000000000^4847 ≤ 1901451219313^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358293859 2500000000 1901451219313 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4907952913/10000000000 : ℝ)^5871 ≤ (42227809199289/100000000000000 : ℝ)^4847 := by
    have hnat : (4907952913 : ℕ)^5871*100000000000000^4847 ≤ 42227809199289^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4907952913 10000000000 42227809199289 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342524489/625000000 : ℝ)^5871 ≤ (48264934692967/100000000000000 : ℝ)^4847 := by
    have hnat : (342524489 : ℕ)^5871*100000000000000^4847 ≤ 48264934692967^4847*625000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342524489 625000000 48264934692967 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-358293859/2500000000 : ℝ), (4907952913/10000000000 : ℝ), (342524489/625000000 : ℝ)] ![(1901451219313/20000000000000 : ℝ), (42227809199289/100000000000000 : ℝ), (48264934692967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-358293859/2500000000 : ℝ)|^5871 ≤ (1901451219313/20000000000000 : ℝ)^4847
        have hw : |(-358293859/2500000000 : ℝ)|=(358293859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4907952913/10000000000 : ℝ)|^5871 ≤ (42227809199289/100000000000000 : ℝ)^4847
        have hw : |(4907952913/10000000000 : ℝ)|=(4907952913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342524489/625000000 : ℝ)|^5871 ≤ (48264934692967/100000000000000 : ℝ)^4847
        have hw : |(342524489/625000000 : ℝ)|=(342524489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_9 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152769113/10000000000 : ℝ)*x 0 + (-1105552941/10000000000 : ℝ)*x 1 + (2740195893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152769113/10000000000 : ℝ)^5871 ≤ (8958494674619/20000000000000 : ℝ)^4847 := by
    have hnat : (5152769113 : ℕ)^5871*20000000000000^4847 ≤ 8958494674619^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152769113 10000000000 8958494674619 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105552941/10000000000 : ℝ)^5871 ≤ (6942592323209/100000000000000 : ℝ)^4847 := by
    have hnat : (1105552941 : ℕ)^5871*100000000000000^4847 ≤ 6942592323209^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105552941 10000000000 6942592323209 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740195893/5000000000 : ℝ)^5871 ≤ (24132467143803/50000000000000 : ℝ)^4847 := by
    have hnat : (2740195893 : ℕ)^5871*50000000000000^4847 ≤ 24132467143803^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740195893 5000000000 24132467143803 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152769113/10000000000 : ℝ), (-1105552941/10000000000 : ℝ), (2740195893/5000000000 : ℝ)] ![(8958494674619/20000000000000 : ℝ), (6942592323209/100000000000000 : ℝ), (24132467143803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152769113/10000000000 : ℝ)|^5871 ≤ (8958494674619/20000000000000 : ℝ)^4847
        have hw : |(5152769113/10000000000 : ℝ)|=(5152769113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1105552941/10000000000 : ℝ)|^5871 ≤ (6942592323209/100000000000000 : ℝ)^4847
        have hw : |(-1105552941/10000000000 : ℝ)|=(1105552941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740195893/5000000000 : ℝ)|^5871 ≤ (24132467143803/50000000000000 : ℝ)^4847
        have hw : |(2740195893/5000000000 : ℝ)|=(2740195893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_10 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (257638469/500000000 : ℝ)*x 0 + (1370097873/2500000000 : ℝ)*x 1 + (-138194123/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257638469/500000000 : ℝ)^5871 ≤ (44792476184443/100000000000000 : ℝ)^4847 := by
    have hnat : (257638469 : ℕ)^5871*100000000000000^4847 ≤ 44792476184443^4847*500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257638469 500000000 44792476184443 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370097873/2500000000 : ℝ)^5871 ≤ (24132465575693/50000000000000 : ℝ)^4847 := by
    have hnat : (1370097873 : ℕ)^5871*50000000000000^4847 ≤ 24132465575693^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370097873 2500000000 24132465575693 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138194123/1250000000 : ℝ)^5871 ≤ (3471296325143/50000000000000 : ℝ)^4847 := by
    have hnat : (138194123 : ℕ)^5871*50000000000000^4847 ≤ 3471296325143^4847*1250000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138194123 1250000000 3471296325143 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257638469/500000000 : ℝ), (1370097873/2500000000 : ℝ), (-138194123/1250000000 : ℝ)] ![(44792476184443/100000000000000 : ℝ), (24132465575693/50000000000000 : ℝ), (3471296325143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257638469/500000000 : ℝ)|^5871 ≤ (44792476184443/100000000000000 : ℝ)^4847
        have hw : |(257638469/500000000 : ℝ)|=(257638469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370097873/2500000000 : ℝ)|^5871 ≤ (24132465575693/50000000000000 : ℝ)^4847
        have hw : |(1370097873/2500000000 : ℝ)|=(1370097873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138194123/1250000000 : ℝ)|^5871 ≤ (3471296325143/50000000000000 : ℝ)^4847
        have hw : |(-138194123/1250000000 : ℝ)|=(138194123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_11 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (95090617/200000000 : ℝ)*x 0 + (1834340061/5000000000 : ℝ)*x 1 + (3668680663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95090617/200000000 : ℝ)^5871 ≤ (40634219143003/100000000000000 : ℝ)^4847 := by
    have hnat : (95090617 : ℕ)^5871*100000000000000^4847 ≤ 40634219143003^4847*200000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95090617 200000000 40634219143003 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1834340061/5000000000 : ℝ)^5871 ≤ (14841443885837/50000000000000 : ℝ)^4847 := by
    have hnat : (1834340061 : ℕ)^5871*50000000000000^4847 ≤ 14841443885837^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834340061 5000000000 14841443885837 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3668680663/10000000000 : ℝ)^5871 ≤ (7420723268397/25000000000000 : ℝ)^4847 := by
    have hnat : (3668680663 : ℕ)^5871*25000000000000^4847 ≤ 7420723268397^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668680663 10000000000 7420723268397 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(95090617/200000000 : ℝ), (1834340061/5000000000 : ℝ), (3668680663/10000000000 : ℝ)] ![(40634219143003/100000000000000 : ℝ), (14841443885837/50000000000000 : ℝ), (7420723268397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(95090617/200000000 : ℝ)|^5871 ≤ (40634219143003/100000000000000 : ℝ)^4847
        have hw : |(95090617/200000000 : ℝ)|=(95090617/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1834340061/5000000000 : ℝ)|^5871 ≤ (14841443885837/50000000000000 : ℝ)^4847
        have hw : |(1834340061/5000000000 : ℝ)|=(1834340061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3668680663/10000000000 : ℝ)|^5871 ≤ (7420723268397/25000000000000 : ℝ)^4847
        have hw : |(3668680663/10000000000 : ℝ)|=(3668680663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_12 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24278451/250000000 : ℝ)*x 0 + (5627338109/10000000000 : ℝ)*x 1 + (637403881/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24278451/250000000 : ℝ)^5871 ≤ (185429661269/3125000000000 : ℝ)^4847 := by
    have hnat : (24278451 : ℕ)^5871*3125000000000^4847 ≤ 185429661269^4847*250000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24278451 250000000 185429661269 3125000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5627338109/10000000000 : ℝ)^5871 ≤ (24918440245041/50000000000000 : ℝ)^4847 := by
    have hnat : (5627338109 : ℕ)^5871*50000000000000^4847 ≤ 24918440245041^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5627338109 10000000000 24918440245041 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637403881/1250000000 : ℝ)^5871 ≤ (11057342584799/25000000000000 : ℝ)^4847 := by
    have hnat : (637403881 : ℕ)^5871*25000000000000^4847 ≤ 11057342584799^4847*1250000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637403881 1250000000 11057342584799 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24278451/250000000 : ℝ), (5627338109/10000000000 : ℝ), (637403881/1250000000 : ℝ)] ![(185429661269/3125000000000 : ℝ), (24918440245041/50000000000000 : ℝ), (11057342584799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24278451/250000000 : ℝ)|^5871 ≤ (185429661269/3125000000000 : ℝ)^4847
        have hw : |(-24278451/250000000 : ℝ)|=(24278451/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5627338109/10000000000 : ℝ)|^5871 ≤ (24918440245041/50000000000000 : ℝ)^4847
        have hw : |(5627338109/10000000000 : ℝ)|=(5627338109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637403881/1250000000 : ℝ)|^5871 ≤ (11057342584799/25000000000000 : ℝ)^4847
        have hw : |(637403881/1250000000 : ℝ)|=(637403881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_13 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407286099/10000000000 : ℝ)*x 0 + (-79949571/625000000 : ℝ)*x 1 + (1019846201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407286099/10000000000 : ℝ)^5871 ≤ (9497237673179/20000000000000 : ℝ)^4847 := by
    have hnat : (5407286099 : ℕ)^5871*20000000000000^4847 ≤ 9497237673179^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407286099 10000000000 9497237673179 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79949571/625000000 : ℝ)^5871 ≤ (1656888347217/20000000000000 : ℝ)^4847 := by
    have hnat : (79949571 : ℕ)^5871*20000000000000^4847 ≤ 1656888347217^4847*625000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79949571 625000000 1656888347217 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019846201/2000000000 : ℝ)^5871 ≤ (4422936988743/10000000000000 : ℝ)^4847 := by
    have hnat : (1019846201 : ℕ)^5871*10000000000000^4847 ≤ 4422936988743^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019846201 2000000000 4422936988743 10000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407286099/10000000000 : ℝ), (-79949571/625000000 : ℝ), (1019846201/2000000000 : ℝ)] ![(9497237673179/20000000000000 : ℝ), (1656888347217/20000000000000 : ℝ), (4422936988743/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407286099/10000000000 : ℝ)|^5871 ≤ (9497237673179/20000000000000 : ℝ)^4847
        have hw : |(5407286099/10000000000 : ℝ)|=(5407286099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79949571/625000000 : ℝ)|^5871 ≤ (1656888347217/20000000000000 : ℝ)^4847
        have hw : |(-79949571/625000000 : ℝ)|=(79949571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019846201/2000000000 : ℝ)|^5871 ≤ (4422936988743/10000000000000 : ℝ)^4847
        have hw : |(1019846201/2000000000 : ℝ)|=(1019846201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_14 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407286321/10000000000 : ℝ)*x 0 + (5099230923/10000000000 : ℝ)*x 1 + (-1279192943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407286321/10000000000 : ℝ)^5871 ≤ (5935773840919/12500000000000 : ℝ)^4847 := by
    have hnat : (5407286321 : ℕ)^5871*12500000000000^4847 ≤ 5935773840919^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407286321 10000000000 5935773840919 12500000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5099230923/10000000000 : ℝ)^5871 ≤ (22114684512961/50000000000000 : ℝ)^4847 := by
    have hnat : (5099230923 : ℕ)^5871*50000000000000^4847 ≤ 22114684512961^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099230923 10000000000 22114684512961 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279192943/10000000000 : ℝ)^5871 ≤ (8284440222093/100000000000000 : ℝ)^4847 := by
    have hnat : (1279192943 : ℕ)^5871*100000000000000^4847 ≤ 8284440222093^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279192943 10000000000 8284440222093 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407286321/10000000000 : ℝ), (5099230923/10000000000 : ℝ), (-1279192943/10000000000 : ℝ)] ![(5935773840919/12500000000000 : ℝ), (22114684512961/50000000000000 : ℝ), (8284440222093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407286321/10000000000 : ℝ)|^5871 ≤ (5935773840919/12500000000000 : ℝ)^4847
        have hw : |(5407286321/10000000000 : ℝ)|=(5407286321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5099230923/10000000000 : ℝ)|^5871 ≤ (22114684512961/50000000000000 : ℝ)^4847
        have hw : |(5099230923/10000000000 : ℝ)|=(5099230923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1279192943/10000000000 : ℝ)|^5871 ≤ (8284440222093/100000000000000 : ℝ)^4847
        have hw : |(-1279192943/10000000000 : ℝ)|=(1279192943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_box_15 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3327903191/10000000000 : ℝ)*x 0 + (4382119311/10000000000 : ℝ)*x 1 + (4382118263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3327903191/10000000000 : ℝ)^5871 ≤ (26376806730027/100000000000000 : ℝ)^4847 := by
    have hnat : (3327903191 : ℕ)^5871*100000000000000^4847 ≤ 26376806730027^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3327903191 10000000000 26376806730027 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4382119311/10000000000 : ℝ)^5871 ≤ (18405800981781/50000000000000 : ℝ)^4847 := by
    have hnat : (4382119311 : ℕ)^5871*50000000000000^4847 ≤ 18405800981781^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382119311 10000000000 18405800981781 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4382118263/10000000000 : ℝ)^5871 ≤ (9202897825009/25000000000000 : ℝ)^4847 := by
    have hnat : (4382118263 : ℕ)^5871*25000000000000^4847 ≤ 9202897825009^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382118263 10000000000 9202897825009 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3327903191/10000000000 : ℝ), (4382119311/10000000000 : ℝ), (4382118263/10000000000 : ℝ)] ![(26376806730027/100000000000000 : ℝ), (18405800981781/50000000000000 : ℝ), (9202897825009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3327903191/10000000000 : ℝ)|^5871 ≤ (26376806730027/100000000000000 : ℝ)^4847
        have hw : |(3327903191/10000000000 : ℝ)|=(3327903191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4382119311/10000000000 : ℝ)|^5871 ≤ (18405800981781/50000000000000 : ℝ)^4847
        have hw : |(4382119311/10000000000 : ℝ)|=(4382119311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4382118263/10000000000 : ℝ)|^5871 ≤ (9202897825009/25000000000000 : ℝ)^4847
        have hw : |(4382118263/10000000000 : ℝ)|=(4382118263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1756_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(17257/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58407/100000 : ℝ) ∧ (20477/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (93009/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1139/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17859/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1139/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1139/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17859/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1139/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1139/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17859/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1139/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1139/12500 : ℝ) ^ (5855/1024 : ℝ) ≤ (28135000103967/25000000000000000000 : ℝ) := by
    have hpowers : (1139/12500 : ℝ)^5855 ≤ (28135000103967/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1139 : ℕ)^5855*25000000000000000000^1024 ≤ 28135000103967^1024*12500^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1139 12500 28135000103967 25000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1139/12500 : ℝ)) (X := (28135000103967/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17859/100000 : ℝ) ^ (5855/1024 : ℝ) ≤ (5275803504614599/100000000000000000000 : ℝ) := by
    have hpowers : (17859/100000 : ℝ)^5855 ≤ (5275803504614599/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17859 : ℕ)^5855*100000000000000000000^1024 ≤ 5275803504614599^1024*100000^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17859 100000 5275803504614599 100000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17859/100000 : ℝ)) (X := (5275803504614599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500028135000103967/12500000000000000000 : ℝ) ≤ (625000246030857/625000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (12500028135000103967/12500000000000000000 : ℝ)^1024 ≤ (625000246030857/625000000000000 : ℝ)^5855 := by
      have hnat : (12500028135000103967 : ℕ)^1024*625000000000000^5855 ≤ 625000246030857^5855*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500028135000103967 12500000000000000000 625000246030857 625000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000246030857/625000000000000 : ℝ)) (X := (12500028135000103967/12500000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100005388343505030467/100000000000000000000 : ℝ) ≤ (5000047118198947/5000000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (100005388343505030467/100000000000000000000 : ℝ)^1024 ≤ (5000047118198947/5000000000000000 : ℝ)^5855 := by
      have hnat : (100005388343505030467 : ℕ)^1024*5000000000000000^5855 ≤ 5000047118198947^5855*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005388343505030467 100000000000000000000 5000047118198947 5000000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000047118198947/5000000000000000 : ℝ)) (X := (100005388343505030467/100000000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50005275803504614599/50000000000000000000 : ℝ) ≤ (2500046134075519/2500000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (50005275803504614599/50000000000000000000 : ℝ)^1024 ≤ (2500046134075519/2500000000000000 : ℝ)^5855 := by
      have hnat : (50005275803504614599 : ℕ)^1024*2500000000000000^5855 ≤ 2500046134075519^5855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005275803504614599 50000000000000000000 2500046134075519 2500000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500046134075519/2500000000000000 : ℝ)) (X := (50005275803504614599/50000000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28135000103967/25000000000000000000 : ℝ) ≤ ((5466774300441042881/5466875000000000000 : ℝ)+2*(45149952091/437350000000000 : ℝ)*(1139/12500 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (5466774300441042881/5466875000000000000 : ℝ)+2*(45149952091/437350000000000 : ℝ)*(1139/12500 : ℝ)=(625000246030857/625000000000000 : ℝ) by norm_num, show 1+2*(28135000103967/25000000000000000000 : ℝ)=(12500028135000103967/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5275803504614599/100000000000000000000 : ℝ)+(28135000103967/25000000000000000000 : ℝ) ≤ ((5466774300441042881/5466875000000000000 : ℝ)+(45149952091/437350000000000 : ℝ)*((17859/100000 : ℝ)+(1139/12500 : ℝ)))^(5855/1024 : ℝ) := by
    rw [show (5466774300441042881/5466875000000000000 : ℝ)+(45149952091/437350000000000 : ℝ)*((17859/100000 : ℝ)+(1139/12500 : ℝ))=(5000047118198947/5000000000000000 : ℝ) by norm_num, show 1+(5275803504614599/100000000000000000000 : ℝ)+(28135000103967/25000000000000000000 : ℝ)=(100005388343505030467/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5275803504614599/100000000000000000000 : ℝ) ≤ ((5466774300441042881/5466875000000000000 : ℝ)+2*(45149952091/437350000000000 : ℝ)*(17859/100000 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (5466774300441042881/5466875000000000000 : ℝ)+2*(45149952091/437350000000000 : ℝ)*(17859/100000 : ℝ)=(2500046134075519/2500000000000000 : ℝ) by norm_num, show 1+2*(5275803504614599/100000000000000000000 : ℝ)=(50005275803504614599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5466774300441042881/5466875000000000000 : ℝ)*(X 1 0+X 2 0)+(45149952091/437350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (1139/12500 : ℝ)) (hi := (17859/100000 : ℝ)) (c := (5466774300441042881/5466875000000000000 : ℝ)) (alpha := (45149952091/437350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5466774300441042881/5466875000000000000 : ℝ)*(X 0 1+X 2 1)+(45149952091/437350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (1139/12500 : ℝ)) (hi := (17859/100000 : ℝ)) (c := (5466774300441042881/5466875000000000000 : ℝ)) (alpha := (45149952091/437350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5466774300441042881/5466875000000000000 : ℝ)*(X 0 2+X 1 2)+(45149952091/437350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (1139/12500 : ℝ)) (hi := (17859/100000 : ℝ)) (c := (5466774300441042881/5466875000000000000 : ℝ)) (alpha := (45149952091/437350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-812496019/10000000000 : ℝ)*X 0 0+(84670047/156250000 : ℝ)*X 0 1+(1083776641/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1298442181/2500000000 : ℝ)*X 1 0+(-7092673/62500000 : ℝ)*X 1 1+(5418883127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((519376879/1000000000 : ℝ)*X 2 0+(2709441559/5000000000 : ℝ)*X 2 1+(-567413801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1133494941/2500000000 : ℝ)*X 0 0+(756841097/2000000000 : ℝ)*X 0 1+(3784205723/10000000000 : ℝ)*X 0 2+(1133494941/2500000000 : ℝ)*X 1 0+(756841097/2000000000 : ℝ)*X 1 1+(3784205723/10000000000 : ℝ)*X 1 2+(1133494941/2500000000 : ℝ)*X 2 0+(756841097/2000000000 : ℝ)*X 2 1+(3784205723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-802933243/5000000000 : ℝ)*X 0 0+(5129160523/10000000000 : ℝ)*X 0 1+(2564579917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5387227369/10000000000 : ℝ)*X 1 0+(-253251839/2000000000 : ℝ)*X 1 1+(1025832047/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5387227223/10000000000 : ℝ)*X 2 0+(2564580117/5000000000 : ℝ)*X 2 1+(-253251879/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3445540341/10000000000 : ℝ)*X 0 0+(865268417/2000000000 : ℝ)*X 0 1+(2163170681/5000000000 : ℝ)*X 0 2+(3445540341/10000000000 : ℝ)*X 1 0+(865268417/2000000000 : ℝ)*X 1 1+(2163170681/5000000000 : ℝ)*X 1 2+(3445540341/10000000000 : ℝ)*X 2 0+(865268417/2000000000 : ℝ)*X 2 1+(2163170681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-358293859/2500000000 : ℝ)*X 0 0+(4907952913/10000000000 : ℝ)*X 0 1+(342524489/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152769113/10000000000 : ℝ)*X 1 0+(-1105552941/10000000000 : ℝ)*X 1 1+(2740195893/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((257638469/500000000 : ℝ)*X 2 0+(1370097873/2500000000 : ℝ)*X 2 1+(-138194123/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((95090617/200000000 : ℝ)*X 0 0+(1834340061/5000000000 : ℝ)*X 0 1+(3668680663/10000000000 : ℝ)*X 0 2+(95090617/200000000 : ℝ)*X 1 0+(1834340061/5000000000 : ℝ)*X 1 1+(3668680663/10000000000 : ℝ)*X 1 2+(95090617/200000000 : ℝ)*X 2 0+(1834340061/5000000000 : ℝ)*X 2 1+(3668680663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-24278451/250000000 : ℝ)*X 0 0+(5627338109/10000000000 : ℝ)*X 0 1+(637403881/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5407286099/10000000000 : ℝ)*X 1 0+(-79949571/625000000 : ℝ)*X 1 1+(1019846201/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5407286321/10000000000 : ℝ)*X 2 0+(5099230923/10000000000 : ℝ)*X 2 1+(-1279192943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3327903191/10000000000 : ℝ)*X 0 0+(4382119311/10000000000 : ℝ)*X 0 1+(4382118263/10000000000 : ℝ)*X 0 2+(3327903191/10000000000 : ℝ)*X 1 0+(4382119311/10000000000 : ℝ)*X 1 1+(4382118263/10000000000 : ℝ)*X 1 2+(3327903191/10000000000 : ℝ)*X 2 0+(4382119311/10000000000 : ℝ)*X 2 1+(4382118263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-17257/25000 : ℝ) ≤ (-18867767525002240323270128765799/27334375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2600307/25000000000000 : ℝ)*(lower0) + (30511299/100000000000000 : ℝ)*(upper3) + (14431613/100000000000000 : ℝ)*(lower4) + (6933127/20000000000000 : ℝ)*(lower5) + (107018143531781/10000000000000 : ℝ)*(major0) + (107018143531781/10000000000000 : ℝ)*(major1) + (107018143531781/10000000000000 : ℝ)*(major2) + (338880061/100000000000000 : ℝ)*(sp1) + (836575606583713/50000000000000 : ℝ)*(sp4) + (1673152195358631/100000000000000 : ℝ)*(sp5) + (334630163812729/20000000000000 : ℝ)*(sp6) + (490218932136417/100000000000000 : ℝ)*(sp7) + (264214253/20000000000000 : ℝ)*(sp8) + (1715175047/100000000000000 : ℝ)*(sp14) + (490218932136417/100000000000000 : ℝ)*(f.failure) + (418288133559673/25000000000000 : ℝ)*(f.sum) + (5666980582397/8747000000000000000000000000 : ℝ)*base65 + (489769848192963561/54668750000000000000000000000000 : ℝ)*base67 + (285051429641276061/54668750000000000000000000000000 : ℝ)*base69 + (203595123236938561/54668750000000000000000000000000 : ℝ)*base71 + (12319897485761/2186750000000000000000000000 : ℝ)*base73 + (102722161504801061/54668750000000000000000000000000 : ℝ)*base75 + (106576902465107311/54668750000000000000000000000000 : ℝ)*base77 + (352911959053613561/54668750000000000000000000000000 : ℝ)*base79 + (4218014132821/4373500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3297961/2000000000000000000000 : ℝ)*base90 + (3297961/2000000000000000000000 : ℝ)*base92 + (3297961/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58407/100000 : ℝ) ≤ (4989347281954835265203546434053/8541992187500000000000000000000 : ℝ) := by norm_num
    linear_combination (994189/12500000000000 : ℝ)*(lower1) + (7717509/100000000000000 : ℝ)*(lower3) + (5403441/50000000000000 : ℝ)*(upper4) + (12521787/100000000000000 : ℝ)*(upper5) + (74830538602871/6250000000000 : ℝ)*(major0) + (74830538602871/6250000000000 : ℝ)*(major1) + (74830538602871/6250000000000 : ℝ)*(major2) + (1826663871967849/100000000000000 : ℝ)*(sp0) + (913332162542449/50000000000000 : ℝ)*(sp1) + (365332804084281/20000000000000 : ℝ)*(sp2) + (548442946880511/100000000000000 : ℝ)*(sp3) + (20444889/25000000000000 : ℝ)*(sp7) + (304663493/100000000000000 : ℝ)*(sp10) + (56639631/12500000000000 : ℝ)*(sp12) + (137110757165017/25000000000000 : ℝ)*(f.failure) + (913332162542449/50000000000000 : ℝ)*(f.sum) + (244248158919837/43735000000000000000000000000 : ℝ)*base65 + (466563961615067279/136671875000000000000000000000000 : ℝ)*base67 + (336122636828286673/68335937500000000000000000000000 : ℝ)*base70 + (94522831985494899/34167968750000000000000000000000 : ℝ)*base72 + (270157144404927/43735000000000000000000000000 : ℝ)*base73 + (648865321276245221/136671875000000000000000000000000 : ℝ)*base76 + (325311906276349173/68335937500000000000000000000000 : ℝ)*base78 + (523507645674526471/136671875000000000000000000000000 : ℝ)*base80 + (34399634289853/43735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6798239/500000000000000000000 : ℝ)*base89 + (6798239/500000000000000000000 : ℝ)*base91 + (6798239/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (20477/25000 : ℝ) ≤ (55974198702359663846827550127783/68335937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5158027/20000000000000 : ℝ)*(upper0) + (4749219/25000000000000 : ℝ)*(lower3) + (13333013/100000000000000 : ℝ)*(upper4) + (575323539817337/50000000000000 : ℝ)*(major0) + (575323539817337/50000000000000 : ℝ)*(major1) + (575323539817337/50000000000000 : ℝ)*(major2) + (4062179913/50000000000000 : ℝ)*(sp1) + (993269493/100000000000000 : ℝ)*(sp3) + (184987857/50000000000000 : ℝ)*(sp4) + (1746911797609609/100000000000000 : ℝ)*(sp8) + (1746904689108077/100000000000000 : ℝ)*(sp9) + (1746912813467903/100000000000000 : ℝ)*(sp10) + (527076905887753/100000000000000 : ℝ)*(sp11) + (645882579/100000000000000 : ℝ)*(sp12) + (105415579831449/20000000000000 : ℝ)*(f.failure) + (1746912813467903/100000000000000 : ℝ)*(f.sum) + (141246716310311/21867500000000000000000000000 : ℝ)*base66 + (150920583539221647/273343750000000000000000000000000 : ℝ)*base67 + (2153285944413377897/273343750000000000000000000000000 : ℝ)*base69 + (1389078944203965853/273343750000000000000000000000000 : ℝ)*base72 + (68121748639161/21867500000000000000000000000 : ℝ)*base74 + (1054208980710997103/273343750000000000000000000000000 : ℝ)*base76 + (1035345457454122103/273343750000000000000000000000000 : ℝ)*base78 + (1003819740095840853/273343750000000000000000000000000 : ℝ)*base80 + (42253817068029/21867500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3069217/400000000000000000000 : ℝ)*base90 + (3069217/400000000000000000000 : ℝ)*base92 + (3069217/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-93009/100000 : ℝ) ≤ (-20338284980988331677059410089/21867500000000000000000000000 : ℝ) := by norm_num
    linear_combination (27387659/100000000000000 : ℝ)*(lower0) + (11041043/20000000000000 : ℝ)*(lower2) + (318289/12500000000000 : ℝ)*(upper3) + (1207937061417877/100000000000000 : ℝ)*(major0) + (1207937061417877/100000000000000 : ℝ)*(major1) + (1207937061417877/100000000000000 : ℝ)*(major2) + (336809009/25000000000000 : ℝ)*(sp0) + (17960131803/100000000000000 : ℝ)*(sp5) + (356095641/3125000000000 : ℝ)*(sp6) + (1452327559/50000000000000 : ℝ)*(sp7) + (94677715341949/5000000000000 : ℝ)*(sp12) + (473384423485803/25000000000000 : ℝ)*(sp13) + (1893544259014503/100000000000000 : ℝ)*(sp14) + (276658932909091/50000000000000 : ℝ)*(sp15) + (553320770473301/100000000000000 : ℝ)*(f.failure) + (236694456759377/12500000000000 : ℝ)*(f.sum) + (12027450900823/21867500000000000000000000000 : ℝ)*base66 + (427845650121678863/546687500000000000000000000000000 : ℝ)*base68 + (1918747889103803863/546687500000000000000000000000000 : ℝ)*base70 + (2058083701029258637/546687500000000000000000000000000 : ℝ)*base71 + (189473009188589/43735000000000000000000000000 : ℝ)*base73 + (2212943840726508637/546687500000000000000000000000000 : ℝ)*base75 + (281359039218741363/546687500000000000000000000000000 : ℝ)*base78 + (3589875062013133637/546687500000000000000000000000000 : ℝ)*base79 + (20280216916941/43735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (18662467/2000000000000000000000 : ℝ)*base89 + (18662467/2000000000000000000000 : ℝ)*base91 + (18662467/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1756_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17859/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17257/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58407/100000 : ℝ) else (20477/25000 : ℝ) ≤ X j i ∧ X j i ≤ (93009/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1756_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1756_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (893/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17257/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58407/100000 : ℝ) else (20477/25000 : ℝ) ≤ X j i ∧ X j i ≤ (93009/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1756_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1756_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (893/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(17257/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58407/100000 : ℝ) else (20477/25000 : ℝ) ≤ X j i ∧ X j i ≤ (93009/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1756_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
