-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1063_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:04:52.60814+00:00
-- url     : https://prove2.me/submissions/292e0f34-7da5-473a-bba4-888c26e83e94

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
theorem support_rectangle_w1063_s0_0 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-239633263/1250000000 : ℝ)*x 0 + (1214554359/2000000000 : ℝ)*x 1 + (4770399781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239633263/1250000000 : ℝ)^129 ≤ (11116838142783/100000000000000 : ℝ)^97 := by
    have hnat : (239633263 : ℕ)^129*100000000000000^97 ≤ 11116838142783^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239633263 1250000000 11116838142783 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214554359/2000000000 : ℝ)^129 ≤ (10302840713419/20000000000000 : ℝ)^97 := by
    have hnat : (1214554359 : ℕ)^129*20000000000000^97 ≤ 10302840713419^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214554359 2000000000 10302840713419 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770399781/10000000000 : ℝ)^129 ≤ (18684479137241/50000000000000 : ℝ)^97 := by
    have hnat : (4770399781 : ℕ)^129*50000000000000^97 ≤ 18684479137241^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770399781 10000000000 18684479137241 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239633263/1250000000 : ℝ), (1214554359/2000000000 : ℝ), (4770399781/10000000000 : ℝ)] ![(11116838142783/100000000000000 : ℝ), (10302840713419/20000000000000 : ℝ), (18684479137241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239633263/1250000000 : ℝ)|^129 ≤ (11116838142783/100000000000000 : ℝ)^97
        have hw : |(-239633263/1250000000 : ℝ)|=(239633263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214554359/2000000000 : ℝ)|^129 ≤ (10302840713419/20000000000000 : ℝ)^97
        have hw : |(1214554359/2000000000 : ℝ)|=(1214554359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770399781/10000000000 : ℝ)|^129 ≤ (18684479137241/50000000000000 : ℝ)^97
        have hw : |(4770399781/10000000000 : ℝ)|=(4770399781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s0_1 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5521244123/10000000000 : ℝ)*x 0 + (-333351179/1250000000 : ℝ)*x 1 + (4770397263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521244123/10000000000 : ℝ)^129 ≤ (22693722602733/50000000000000 : ℝ)^97 := by
    have hnat : (5521244123 : ℕ)^129*50000000000000^97 ≤ 22693722602733^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521244123 10000000000 22693722602733 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (333351179/1250000000 : ℝ)^129 ≤ (17243622743349/100000000000000 : ℝ)^97 := by
    have hnat : (333351179 : ℕ)^129*100000000000000^97 ≤ 17243622743349^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333351179 1250000000 17243622743349 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770397263/10000000000 : ℝ)^129 ≤ (18684466021287/50000000000000 : ℝ)^97 := by
    have hnat : (4770397263 : ℕ)^129*50000000000000^97 ≤ 18684466021287^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770397263 10000000000 18684466021287 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521244123/10000000000 : ℝ), (-333351179/1250000000 : ℝ), (4770397263/10000000000 : ℝ)] ![(22693722602733/50000000000000 : ℝ), (17243622743349/100000000000000 : ℝ), (18684466021287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521244123/10000000000 : ℝ)|^129 ≤ (22693722602733/50000000000000 : ℝ)^97
        have hw : |(5521244123/10000000000 : ℝ)|=(5521244123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-333351179/1250000000 : ℝ)|^129 ≤ (17243622743349/100000000000000 : ℝ)^97
        have hw : |(-333351179/1250000000 : ℝ)|=(333351179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770397263/10000000000 : ℝ)|^129 ≤ (18684466021287/50000000000000 : ℝ)^97
        have hw : |(4770397263/10000000000 : ℝ)|=(4770397263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s0_2 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1380310313/2500000000 : ℝ)*x 0 + (4770399979/10000000000 : ℝ)*x 1 + (-2666809791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380310313/2500000000 : ℝ)^129 ≤ (22693706909229/50000000000000 : ℝ)^97 := by
    have hnat : (1380310313 : ℕ)^129*50000000000000^97 ≤ 22693706909229^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380310313 2500000000 22693706909229 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4770399979/10000000000 : ℝ)^129 ≤ (18684480168599/50000000000000 : ℝ)^97 := by
    have hnat : (4770399979 : ℕ)^129*50000000000000^97 ≤ 18684480168599^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770399979 10000000000 18684480168599 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2666809791/10000000000 : ℝ)^129 ≤ (17243625830437/100000000000000 : ℝ)^97 := by
    have hnat : (2666809791 : ℕ)^129*100000000000000^97 ≤ 17243625830437^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666809791 10000000000 17243625830437 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380310313/2500000000 : ℝ), (4770399979/10000000000 : ℝ), (-2666809791/10000000000 : ℝ)] ![(22693706909229/50000000000000 : ℝ), (18684480168599/50000000000000 : ℝ), (17243625830437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380310313/2500000000 : ℝ)|^129 ≤ (22693706909229/50000000000000 : ℝ)^97
        have hw : |(1380310313/2500000000 : ℝ)|=(1380310313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4770399979/10000000000 : ℝ)|^129 ≤ (18684480168599/50000000000000 : ℝ)^97
        have hw : |(4770399979/10000000000 : ℝ)|=(4770399979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2666809791/10000000000 : ℝ)|^129 ≤ (17243625830437/100000000000000 : ℝ)^97
        have hw : |(-2666809791/10000000000 : ℝ)|=(2666809791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s0_3 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (420745871/1000000000 : ℝ)*x 0 + (781257619/2500000000 : ℝ)*x 1 + (5675966339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420745871/1000000000 : ℝ)^129 ≤ (3952712173329/12500000000000 : ℝ)^97 := by
    have hnat : (420745871 : ℕ)^129*12500000000000^97 ≤ 3952712173329^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420745871 1000000000 3952712173329 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781257619/2500000000 : ℝ)^129 ≤ (425831941313/2000000000000 : ℝ)^97 := by
    have hnat : (781257619 : ℕ)^129*2000000000000^97 ≤ 425831941313^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781257619 2500000000 425831941313 2000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675966339/10000000000 : ℝ)^129 ≤ (47086705531971/100000000000000 : ℝ)^97 := by
    have hnat : (5675966339 : ℕ)^129*100000000000000^97 ≤ 47086705531971^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675966339 10000000000 47086705531971 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420745871/1000000000 : ℝ), (781257619/2500000000 : ℝ), (5675966339/10000000000 : ℝ)] ![(3952712173329/12500000000000 : ℝ), (425831941313/2000000000000 : ℝ), (47086705531971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420745871/1000000000 : ℝ)|^129 ≤ (3952712173329/12500000000000 : ℝ)^97
        have hw : |(420745871/1000000000 : ℝ)|=(420745871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781257619/2500000000 : ℝ)|^129 ≤ (425831941313/2000000000000 : ℝ)^97
        have hw : |(781257619/2500000000 : ℝ)|=(781257619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5675966339/10000000000 : ℝ)|^129 ≤ (47086705531971/100000000000000 : ℝ)^97
        have hw : |(5675966339/10000000000 : ℝ)|=(5675966339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s0_4 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-384490071/2000000000 : ℝ)*x 0 + (2402014647/5000000000 : ℝ)*x 1 + (6037965021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384490071/2000000000 : ℝ)^129 ≤ (1394797530883/12500000000000 : ℝ)^97 := by
    have hnat : (384490071 : ℕ)^129*12500000000000^97 ≤ 1394797530883^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384490071 2000000000 1394797530883 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2402014647/5000000000 : ℝ)^129 ≤ (37719709091963/100000000000000 : ℝ)^97 := by
    have hnat : (2402014647 : ℕ)^129*100000000000000^97 ≤ 37719709091963^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402014647 5000000000 37719709091963 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6037965021/10000000000 : ℝ)^129 ≤ (25560955325737/50000000000000 : ℝ)^97 := by
    have hnat : (6037965021 : ℕ)^129*50000000000000^97 ≤ 25560955325737^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6037965021 10000000000 25560955325737 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-384490071/2000000000 : ℝ), (2402014647/5000000000 : ℝ), (6037965021/10000000000 : ℝ)] ![(1394797530883/12500000000000 : ℝ), (37719709091963/100000000000000 : ℝ), (25560955325737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-384490071/2000000000 : ℝ)|^129 ≤ (1394797530883/12500000000000 : ℝ)^97
        have hw : |(-384490071/2000000000 : ℝ)|=(384490071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2402014647/5000000000 : ℝ)|^129 ≤ (37719709091963/100000000000000 : ℝ)^97
        have hw : |(2402014647/5000000000 : ℝ)|=(2402014647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6037965021/10000000000 : ℝ)|^129 ≤ (25560955325737/50000000000000 : ℝ)^97
        have hw : |(6037965021/10000000000 : ℝ)|=(6037965021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s0_5 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5167774487/10000000000 : ℝ)*x 0 + (-87452973/625000000 : ℝ)*x 1 + (3018981501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167774487/10000000000 : ℝ)^129 ≤ (20782284549299/50000000000000 : ℝ)^97 := by
    have hnat : (5167774487 : ℕ)^129*50000000000000^97 ≤ 20782284549299^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167774487 10000000000 20782284549299 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87452973/625000000 : ℝ)^129 ≤ (7313542978493/100000000000000 : ℝ)^97 := by
    have hnat : (87452973 : ℕ)^129*100000000000000^97 ≤ 7313542978493^97*625000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87452973 625000000 7313542978493 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3018981501/5000000000 : ℝ)^129 ≤ (51121887917741/100000000000000 : ℝ)^97 := by
    have hnat : (3018981501 : ℕ)^129*100000000000000^97 ≤ 51121887917741^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3018981501 5000000000 51121887917741 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167774487/10000000000 : ℝ), (-87452973/625000000 : ℝ), (3018981501/5000000000 : ℝ)] ![(20782284549299/50000000000000 : ℝ), (7313542978493/100000000000000 : ℝ), (51121887917741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167774487/10000000000 : ℝ)|^129 ≤ (20782284549299/50000000000000 : ℝ)^97
        have hw : |(5167774487/10000000000 : ℝ)|=(5167774487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87452973/625000000 : ℝ)|^129 ≤ (7313542978493/100000000000000 : ℝ)^97
        have hw : |(-87452973/625000000 : ℝ)|=(87452973/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3018981501/5000000000 : ℝ)|^129 ≤ (51121887917741/100000000000000 : ℝ)^97
        have hw : |(3018981501/5000000000 : ℝ)|=(3018981501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s0_6 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2583887467/5000000000 : ℝ)*x 0 + (6037963831/10000000000 : ℝ)*x 1 + (-1399245537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583887467/5000000000 : ℝ)^129 ≤ (4156457387989/10000000000000 : ℝ)^97 := by
    have hnat : (2583887467 : ℕ)^129*10000000000000^97 ≤ 4156457387989^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583887467 5000000000 4156457387989 10000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6037963831/10000000000 : ℝ)^129 ≤ (12780474313049/25000000000000 : ℝ)^97 := by
    have hnat : (6037963831 : ℕ)^129*25000000000000^97 ≤ 12780474313049^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6037963831 10000000000 12780474313049 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399245537/10000000000 : ℝ)^129 ≤ (7313528860887/100000000000000 : ℝ)^97 := by
    have hnat : (1399245537 : ℕ)^129*100000000000000^97 ≤ 7313528860887^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399245537 10000000000 7313528860887 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583887467/5000000000 : ℝ), (6037963831/10000000000 : ℝ), (-1399245537/10000000000 : ℝ)] ![(4156457387989/10000000000000 : ℝ), (12780474313049/25000000000000 : ℝ), (7313528860887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583887467/5000000000 : ℝ)|^129 ≤ (4156457387989/10000000000000 : ℝ)^97
        have hw : |(2583887467/5000000000 : ℝ)|=(2583887467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6037963831/10000000000 : ℝ)|^129 ≤ (12780474313049/25000000000000 : ℝ)^97
        have hw : |(6037963831/10000000000 : ℝ)|=(6037963831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1399245537/10000000000 : ℝ)|^129 ≤ (7313528860887/100000000000000 : ℝ)^97
        have hw : |(-1399245537/10000000000 : ℝ)|=(1399245537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s0_7 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (843599939/2000000000 : ℝ)*x 0 + (56100983/100000000 : ℝ)*x 1 + (3193200881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843599939/2000000000 : ℝ)^129 ≤ (15863549082777/50000000000000 : ℝ)^97 := by
    have hnat : (843599939 : ℕ)^129*50000000000000^97 ≤ 15863549082777^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843599939 2000000000 15863549082777 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56100983/100000000 : ℝ)^129 ≤ (46361406797557/100000000000000 : ℝ)^97 := by
    have hnat : (56100983 : ℕ)^129*100000000000000^97 ≤ 46361406797557^97*100000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56100983 100000000 46361406797557 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3193200881/10000000000 : ℝ)^129 ≤ (547787375497/2500000000000 : ℝ)^97 := by
    have hnat : (3193200881 : ℕ)^129*2500000000000^97 ≤ 547787375497^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3193200881 10000000000 547787375497 2500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843599939/2000000000 : ℝ), (56100983/100000000 : ℝ), (3193200881/10000000000 : ℝ)] ![(15863549082777/50000000000000 : ℝ), (46361406797557/100000000000000 : ℝ), (547787375497/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843599939/2000000000 : ℝ)|^129 ≤ (15863549082777/50000000000000 : ℝ)^97
        have hw : |(843599939/2000000000 : ℝ)|=(843599939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56100983/100000000 : ℝ)|^129 ≤ (46361406797557/100000000000000 : ℝ)^97
        have hw : |(56100983/100000000 : ℝ)|=(56100983/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3193200881/10000000000 : ℝ)|^129 ≤ (547787375497/2500000000000 : ℝ)^97
        have hw : |(3193200881/10000000000 : ℝ)|=(3193200881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1063_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (21/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28121/100000 : ℝ)*pair X 0 0 := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8255/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8255 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8255*1^2048 ≤ 0^2048*1^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8255/2048 : ℝ) ≤ (2488849562713134033/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8255 ≤ (2488849562713134033/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8255*100000000000000000000^2048 ≤ 2488849562713134033^2048*5^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2488849562713134033 100000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2488849562713134033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8255 := by
      have hnat : (1 : ℕ)^2048*1^8255 ≤ 1^8255*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102488849562713134033/100000000000000000000 : ℝ) ≤ (10061176882383841/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (102488849562713134033/100000000000000000000 : ℝ)^2048 ≤ (10061176882383841/10000000000000000 : ℝ)^8255 := by
      have hnat : (102488849562713134033 : ℕ)^2048*10000000000000000^8255 ≤ 10061176882383841^8255*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102488849562713134033 100000000000000000000 10061176882383841 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061176882383841/10000000000000000 : ℝ)) (X := (102488849562713134033/100000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52488849562713134033/50000000000000000000 : ℝ) ≤ (5061176882383841/5000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (52488849562713134033/50000000000000000000 : ℝ)^2048 ≤ (5061176882383841/5000000000000000 : ℝ)^8255 := by
      have hnat : (52488849562713134033 : ℕ)^2048*5000000000000000^8255 ≤ 5061176882383841^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52488849562713134033 50000000000000000000 5061176882383841 5000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061176882383841/5000000000000000 : ℝ)) (X := (52488849562713134033/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(61176882383841/4000000000000000 : ℝ)*(0 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(61176882383841/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2488849562713134033/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(61176882383841/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8255/2048 : ℝ) := by
    rw [show (1 : ℝ)+(61176882383841/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10061176882383841/10000000000000000 : ℝ) by norm_num, show 1+(2488849562713134033/100000000000000000000 : ℝ)+(0 : ℝ)=(102488849562713134033/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2488849562713134033/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(61176882383841/4000000000000000 : ℝ)*(2/5 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(61176882383841/4000000000000000 : ℝ)*(2/5 : ℝ)=(5061176882383841/5000000000000000 : ℝ) by norm_num, show 1+2*(2488849562713134033/100000000000000000000 : ℝ)=(52488849562713134033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(61176882383841/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61176882383841/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(61176882383841/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61176882383841/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(61176882383841/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61176882383841/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-239633263/1250000000 : ℝ)*X 0 0+(1214554359/2000000000 : ℝ)*X 0 1+(4770399781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5521244123/10000000000 : ℝ)*X 1 0+(-333351179/1250000000 : ℝ)*X 1 1+(4770397263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1380310313/2500000000 : ℝ)*X 2 0+(4770399979/10000000000 : ℝ)*X 2 1+(-2666809791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((420745871/1000000000 : ℝ)*X 0 0+(781257619/2500000000 : ℝ)*X 0 1+(5675966339/10000000000 : ℝ)*X 0 2+(420745871/1000000000 : ℝ)*X 1 0+(781257619/2500000000 : ℝ)*X 1 1+(5675966339/10000000000 : ℝ)*X 1 2+(420745871/1000000000 : ℝ)*X 2 0+(781257619/2500000000 : ℝ)*X 2 1+(5675966339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-384490071/2000000000 : ℝ)*X 0 0+(2402014647/5000000000 : ℝ)*X 0 1+(6037965021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5167774487/10000000000 : ℝ)*X 1 0+(-87452973/625000000 : ℝ)*X 1 1+(3018981501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2583887467/5000000000 : ℝ)*X 2 0+(6037963831/10000000000 : ℝ)*X 2 1+(-1399245537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((843599939/2000000000 : ℝ)*X 0 0+(56100983/100000000 : ℝ)*X 0 1+(3193200881/10000000000 : ℝ)*X 0 2+(843599939/2000000000 : ℝ)*X 1 0+(56100983/100000000 : ℝ)*X 1 1+(3193200881/10000000000 : ℝ)*X 1 2+(843599939/2000000000 : ℝ)*X 2 0+(56100983/100000000 : ℝ)*X 2 1+(3193200881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (461676653383811436994143/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91630359/50000000000000 : ℝ)*(base1) + (442224927/50000000000000 : ℝ)*(base19) + (222503543/50000000000000 : ℝ)*(base23) + (10737849/5000000000000 : ℝ)*(base37) + (115457/1000000000000 : ℝ)*(upper3) + (579922823742059/100000000000000 : ℝ)*(major0) + (579922823742059/100000000000000 : ℝ)*(major1) + (579922823742059/100000000000000 : ℝ)*(major2) + (767831575452181/100000000000000 : ℝ)*(sp0) + (767831850658413/100000000000000 : ℝ)*(sp1) + (191957915633193/25000000000000 : ℝ)*(sp2) + (98003090116483/25000000000000 : ℝ)*(sp3) + (335729201/25000000000000 : ℝ)*(sp4) + (627568409/100000000000000 : ℝ)*(sp6) + (39201275848363/10000000000000 : ℝ)*(f.failure) + (767832735108267/100000000000000 : ℝ)*(f.sum) + (98782118468619/200000000000000000000000000000 : ℝ)*base65 + (887014052468619/400000000000000000000000000000 : ℝ)*base67 + (10231263531381/400000000000000000000000000000 : ℝ)*base70 + (215098206068619/400000000000000000000000000000 : ℝ)*base71 + (126229570468619/200000000000000000000000000000 : ℝ)*base73 + (106086613131381/400000000000000000000000000000 : ℝ)*base76 + (10292705668619/400000000000000000000000000000 : ℝ)*base77 + (612239894068619/400000000000000000000000000000 : ℝ)*base79 + (42502318931381/200000000000000000000000000000 : ℝ)*base82 + (5222797/1000000000000000000000 : ℝ)*base90 + (5222797/1000000000000000000000 : ℝ)*base92 + (5222797/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82980127482455357506683/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11759601/50000000000000 : ℝ)*(base1) + (186645579/12500000000000 : ℝ)*(base19) + (50779171/3125000000000 : ℝ)*(base23) + (243001869/100000000000000 : ℝ)*(base45) + (34154419/20000000000000 : ℝ)*(upper3) + (293850613/100000000000000 : ℝ)*(upper5) + (76510409783693/12500000000000 : ℝ)*(major0) + (76510409783693/12500000000000 : ℝ)*(major1) + (76510409783693/12500000000000 : ℝ)*(major2) + (901634271/100000000000000 : ℝ)*(sp2) + (405206984391281/50000000000000 : ℝ)*(sp4) + (101301556512341/12500000000000 : ℝ)*(sp5) + (12662678417119/1562500000000 : ℝ)*(sp6) + (413752366476179/100000000000000 : ℝ)*(sp7) + (206876194997691/50000000000000 : ℝ)*(f.failure) + (810413945263359/100000000000000 : ℝ)*(f.sum) + (64085611129813/25000000000000000000000000000 : ℝ)*base65 + (56248662104813/50000000000000000000000000000 : ℝ)*base67 + (316433133454813/50000000000000000000000000000 : ℝ)*base69 + (93871111454813/50000000000000000000000000000 : ℝ)*base71 + (35674453604813/25000000000000000000000000000 : ℝ)*base73 + (236208250754813/50000000000000000000000000000 : ℝ)*base75 + (171916906454813/50000000000000000000000000000 : ℝ)*base77 + (321949963254813/50000000000000000000000000000 : ℝ)*base79 + (244514494854813/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (13821571/5000000000000000000000 : ℝ)*base89 + (13821571/5000000000000000000000 : ℝ)*base91 + (13821571/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1063_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (21/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1063_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1063_s1_0 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-85096517/400000000 : ℝ)*x 0 + (357697763/625000000 : ℝ)*x 1 + (2492648803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85096517/400000000 : ℝ)^129 ≤ (2553537114919/20000000000000 : ℝ)^97 := by
    have hnat : (85096517 : ℕ)^129*20000000000000^97 ≤ 2553537114919^97*400000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85096517 400000000 2553537114919 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357697763/625000000 : ℝ)^129 ≤ (47608131954543/100000000000000 : ℝ)^97 := by
    have hnat : (357697763 : ℕ)^129*100000000000000^97 ≤ 47608131954543^97*625000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357697763 625000000 47608131954543 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2492648803/5000000000 : ℝ)^129 ≤ (9906045613783/25000000000000 : ℝ)^97 := by
    have hnat : (2492648803 : ℕ)^129*25000000000000^97 ≤ 9906045613783^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492648803 5000000000 9906045613783 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85096517/400000000 : ℝ), (357697763/625000000 : ℝ), (2492648803/5000000000 : ℝ)] ![(2553537114919/20000000000000 : ℝ), (47608131954543/100000000000000 : ℝ), (9906045613783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85096517/400000000 : ℝ)|^129 ≤ (2553537114919/20000000000000 : ℝ)^97
        have hw : |(-85096517/400000000 : ℝ)|=(85096517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(357697763/625000000 : ℝ)|^129 ≤ (47608131954543/100000000000000 : ℝ)^97
        have hw : |(357697763/625000000 : ℝ)|=(357697763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2492648803/5000000000 : ℝ)|^129 ≤ (9906045613783/25000000000000 : ℝ)^97
        have hw : |(2492648803/5000000000 : ℝ)|=(2492648803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_1 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (677934871/1250000000 : ℝ)*x 0 + (-1263626743/5000000000 : ℝ)*x 1 + (623162241/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677934871/1250000000 : ℝ)^129 ≤ (44321768524017/100000000000000 : ℝ)^97 := by
    have hnat : (677934871 : ℕ)^129*100000000000000^97 ≤ 44321768524017^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677934871 1250000000 44321768524017 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263626743/5000000000 : ℝ)^129 ≤ (16054045602109/100000000000000 : ℝ)^97 := by
    have hnat : (1263626743 : ℕ)^129*100000000000000^97 ≤ 16054045602109^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263626743 5000000000 16054045602109 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623162241/1250000000 : ℝ)^129 ≤ (2476511616173/6250000000000 : ℝ)^97 := by
    have hnat : (623162241 : ℕ)^129*6250000000000^97 ≤ 2476511616173^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623162241 1250000000 2476511616173 6250000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677934871/1250000000 : ℝ), (-1263626743/5000000000 : ℝ), (623162241/1250000000 : ℝ)] ![(44321768524017/100000000000000 : ℝ), (16054045602109/100000000000000 : ℝ), (2476511616173/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677934871/1250000000 : ℝ)|^129 ≤ (44321768524017/100000000000000 : ℝ)^97
        have hw : |(677934871/1250000000 : ℝ)|=(677934871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1263626743/5000000000 : ℝ)|^129 ≤ (16054045602109/100000000000000 : ℝ)^97
        have hw : |(-1263626743/5000000000 : ℝ)|=(1263626743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(623162241/1250000000 : ℝ)|^129 ≤ (2476511616173/6250000000000 : ℝ)^97
        have hw : |(623162241/1250000000 : ℝ)|=(623162241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_2 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2711739757/5000000000 : ℝ)*x 0 + (4985297301/10000000000 : ℝ)*x 1 + (-2527253569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711739757/5000000000 : ℝ)^129 ≤ (44321774458047/100000000000000 : ℝ)^97 := by
    have hnat : (2711739757 : ℕ)^129*100000000000000^97 ≤ 44321774458047^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711739757 5000000000 44321774458047 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4985297301/10000000000 : ℝ)^129 ≤ (4953022403899/12500000000000 : ℝ)^97 := by
    have hnat : (4985297301 : ℕ)^129*12500000000000^97 ≤ 4953022403899^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985297301 10000000000 4953022403899 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2527253569/10000000000 : ℝ)^129 ≤ (4013511575823/25000000000000 : ℝ)^97 := by
    have hnat : (2527253569 : ℕ)^129*25000000000000^97 ≤ 4013511575823^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527253569 10000000000 4013511575823 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711739757/5000000000 : ℝ), (4985297301/10000000000 : ℝ), (-2527253569/10000000000 : ℝ)] ![(44321774458047/100000000000000 : ℝ), (4953022403899/12500000000000 : ℝ), (4013511575823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711739757/5000000000 : ℝ)|^129 ≤ (44321774458047/100000000000000 : ℝ)^97
        have hw : |(2711739757/5000000000 : ℝ)|=(2711739757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4985297301/10000000000 : ℝ)|^129 ≤ (4953022403899/12500000000000 : ℝ)^97
        have hw : |(4985297301/10000000000 : ℝ)|=(4985297301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2527253569/10000000000 : ℝ)|^129 ≤ (4013511575823/25000000000000 : ℝ)^97
        have hw : |(-2527253569/10000000000 : ℝ)|=(2527253569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_3 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (864810099/2000000000 : ℝ)*x 0 + (732392301/2000000000 : ℝ)*x 1 + (510721473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864810099/2000000000 : ℝ)^129 ≤ (2049520473517/6250000000000 : ℝ)^97 := by
    have hnat : (864810099 : ℕ)^129*6250000000000^97 ≤ 2049520473517^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864810099 2000000000 2049520473517 6250000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (732392301/2000000000 : ℝ)^129 ≤ (13144809682933/50000000000000 : ℝ)^97 := by
    have hnat : (732392301 : ℕ)^129*50000000000000^97 ≤ 13144809682933^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732392301 2000000000 13144809682933 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510721473/1000000000 : ℝ)^129 ≤ (8183610607421/20000000000000 : ℝ)^97 := by
    have hnat : (510721473 : ℕ)^129*20000000000000^97 ≤ 8183610607421^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510721473 1000000000 8183610607421 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864810099/2000000000 : ℝ), (732392301/2000000000 : ℝ), (510721473/1000000000 : ℝ)] ![(2049520473517/6250000000000 : ℝ), (13144809682933/50000000000000 : ℝ), (8183610607421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864810099/2000000000 : ℝ)|^129 ≤ (2049520473517/6250000000000 : ℝ)^97
        have hw : |(864810099/2000000000 : ℝ)|=(864810099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(732392301/2000000000 : ℝ)|^129 ≤ (13144809682933/50000000000000 : ℝ)^97
        have hw : |(732392301/2000000000 : ℝ)|=(732392301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(510721473/1000000000 : ℝ)|^129 ≤ (8183610607421/20000000000000 : ℝ)^97
        have hw : |(510721473/1000000000 : ℝ)|=(510721473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_4 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128339757/10000000000 : ℝ)*x 0 + (4995678907/10000000000 : ℝ)*x 1 + (2856284827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128339757/10000000000 : ℝ)^129 ≤ (12775083510877/100000000000000 : ℝ)^97 := by
    have hnat : (2128339757 : ℕ)^129*100000000000000^97 ≤ 12775083510877^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128339757 10000000000 12775083510877 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4995678907/10000000000 : ℝ)^129 ≤ (19866976783587/50000000000000 : ℝ)^97 := by
    have hnat : (4995678907 : ℕ)^129*50000000000000^97 ≤ 19866976783587^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4995678907 10000000000 19866976783587 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2856284827/5000000000 : ℝ)^129 ≤ (47490962906043/100000000000000 : ℝ)^97 := by
    have hnat : (2856284827 : ℕ)^129*100000000000000^97 ≤ 47490962906043^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856284827 5000000000 47490962906043 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128339757/10000000000 : ℝ), (4995678907/10000000000 : ℝ), (2856284827/5000000000 : ℝ)] ![(12775083510877/100000000000000 : ℝ), (19866976783587/50000000000000 : ℝ), (47490962906043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128339757/10000000000 : ℝ)|^129 ≤ (12775083510877/100000000000000 : ℝ)^97
        have hw : |(-2128339757/10000000000 : ℝ)|=(2128339757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4995678907/10000000000 : ℝ)|^129 ≤ (19866976783587/50000000000000 : ℝ)^97
        have hw : |(4995678907/10000000000 : ℝ)|=(4995678907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2856284827/5000000000 : ℝ)|^129 ≤ (47490962906043/100000000000000 : ℝ)^97
        have hw : |(2856284827/5000000000 : ℝ)|=(2856284827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_5 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2617534383/5000000000 : ℝ)*x 0 + (-1799979643/10000000000 : ℝ)*x 1 + (2856285647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617534383/5000000000 : ℝ)^129 ≤ (10571479342783/25000000000000 : ℝ)^97 := by
    have hnat : (2617534383 : ℕ)^129*25000000000000^97 ≤ 10571479342783^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617534383 5000000000 10571479342783 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799979643/10000000000 : ℝ)^129 ≤ (10223101573307/100000000000000 : ℝ)^97 := by
    have hnat : (1799979643 : ℕ)^129*100000000000000^97 ≤ 10223101573307^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799979643 10000000000 10223101573307 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2856285647/5000000000 : ℝ)^129 ≤ (2374549051893/5000000000000 : ℝ)^97 := by
    have hnat : (2856285647 : ℕ)^129*5000000000000^97 ≤ 2374549051893^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856285647 5000000000 2374549051893 5000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617534383/5000000000 : ℝ), (-1799979643/10000000000 : ℝ), (2856285647/5000000000 : ℝ)] ![(10571479342783/25000000000000 : ℝ), (10223101573307/100000000000000 : ℝ), (2374549051893/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617534383/5000000000 : ℝ)|^129 ≤ (10571479342783/25000000000000 : ℝ)^97
        have hw : |(2617534383/5000000000 : ℝ)|=(2617534383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1799979643/10000000000 : ℝ)|^129 ≤ (10223101573307/100000000000000 : ℝ)^97
        have hw : |(-1799979643/10000000000 : ℝ)|=(1799979643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2856285647/5000000000 : ℝ)|^129 ≤ (2374549051893/5000000000000 : ℝ)^97
        have hw : |(2856285647/5000000000 : ℝ)|=(2856285647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_6 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1308766687/2500000000 : ℝ)*x 0 + (71407169/125000000 : ℝ)*x 1 + (-359995851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308766687/2500000000 : ℝ)^129 ≤ (10571473923367/25000000000000 : ℝ)^97 := by
    have hnat : (1308766687 : ℕ)^129*25000000000000^97 ≤ 10571473923367^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308766687 2500000000 10571473923367 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71407169/125000000 : ℝ)^129 ≤ (23745502824243/50000000000000 : ℝ)^97 := by
    have hnat : (71407169 : ℕ)^129*50000000000000^97 ≤ 23745502824243^97*125000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71407169 125000000 23745502824243 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359995851/2000000000 : ℝ)^129 ≤ (2555774660663/25000000000000 : ℝ)^97 := by
    have hnat : (359995851 : ℕ)^129*25000000000000^97 ≤ 2555774660663^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359995851 2000000000 2555774660663 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308766687/2500000000 : ℝ), (71407169/125000000 : ℝ), (-359995851/2000000000 : ℝ)] ![(10571473923367/25000000000000 : ℝ), (23745502824243/50000000000000 : ℝ), (2555774660663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308766687/2500000000 : ℝ)|^129 ≤ (10571473923367/25000000000000 : ℝ)^97
        have hw : |(1308766687/2500000000 : ℝ)|=(1308766687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71407169/125000000 : ℝ)|^129 ≤ (23745502824243/50000000000000 : ℝ)^97
        have hw : |(71407169/125000000 : ℝ)|=(71407169/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-359995851/2000000000 : ℝ)|^129 ≤ (2555774660663/25000000000000 : ℝ)^97
        have hw : |(-359995851/2000000000 : ℝ)|=(359995851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_7 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (432586201/1000000000 : ℝ)*x 0 + (2034751/4000000 : ℝ)*x 1 + (29461677/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432586201/1000000000 : ℝ)^129 ≤ (2050662434911/6250000000000 : ℝ)^97 := by
    have hnat : (432586201 : ℕ)^129*6250000000000^97 ≤ 2050662434911^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432586201 1000000000 2050662434911 6250000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034751/4000000 : ℝ)^129 ≤ (5087688077617/12500000000000 : ℝ)^97 := by
    have hnat : (2034751 : ℕ)^129*12500000000000^97 ≤ 5087688077617^97*4000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034751 4000000 5087688077617 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29461677/80000000 : ℝ)^129 ≤ (13243948203449/50000000000000 : ℝ)^97 := by
    have hnat : (29461677 : ℕ)^129*50000000000000^97 ≤ 13243948203449^97*80000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29461677 80000000 13243948203449 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432586201/1000000000 : ℝ), (2034751/4000000 : ℝ), (29461677/80000000 : ℝ)] ![(2050662434911/6250000000000 : ℝ), (5087688077617/12500000000000 : ℝ), (13243948203449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432586201/1000000000 : ℝ)|^129 ≤ (2050662434911/6250000000000 : ℝ)^97
        have hw : |(432586201/1000000000 : ℝ)|=(432586201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2034751/4000000 : ℝ)|^129 ≤ (5087688077617/12500000000000 : ℝ)^97
        have hw : |(2034751/4000000 : ℝ)|=(2034751/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29461677/80000000 : ℝ)|^129 ≤ (13243948203449/50000000000000 : ℝ)^97
        have hw : |(29461677/80000000 : ℝ)|=(29461677/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_8 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2210399/2500000000 : ℝ)*x 0 + (1372456191/2500000000 : ℝ)*x 1 + (6374618123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210399/2500000000 : ℝ)^129 ≤ (1738723697/20000000000000 : ℝ)^97 := by
    have hnat : (2210399 : ℕ)^129*20000000000000^97 ≤ 1738723697^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210399 2500000000 1738723697 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372456191/2500000000 : ℝ)^129 ≤ (11261069511927/25000000000000 : ℝ)^97 := by
    have hnat : (1372456191 : ℕ)^129*25000000000000^97 ≤ 11261069511927^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372456191 2500000000 11261069511927 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6374618123/10000000000 : ℝ)^129 ≤ (3434189269847/6250000000000 : ℝ)^97 := by
    have hnat : (6374618123 : ℕ)^129*6250000000000^97 ≤ 3434189269847^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6374618123 10000000000 3434189269847 6250000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2210399/2500000000 : ℝ), (1372456191/2500000000 : ℝ), (6374618123/10000000000 : ℝ)] ![(1738723697/20000000000000 : ℝ), (11261069511927/25000000000000 : ℝ), (3434189269847/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2210399/2500000000 : ℝ)|^129 ≤ (1738723697/20000000000000 : ℝ)^97
        have hw : |(2210399/2500000000 : ℝ)|=(2210399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372456191/2500000000 : ℝ)|^129 ≤ (11261069511927/25000000000000 : ℝ)^97
        have hw : |(1372456191/2500000000 : ℝ)|=(1372456191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6374618123/10000000000 : ℝ)|^129 ≤ (3434189269847/6250000000000 : ℝ)^97
        have hw : |(6374618123/10000000000 : ℝ)|=(6374618123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_9 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (963299781/10000000000 : ℝ)*x 0 + (-34851131/78125000 : ℝ)*x 1 + (6927034679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963299781/10000000000 : ℝ)^129 ≤ (2225755806669/50000000000000 : ℝ)^97 := by
    have hnat : (963299781 : ℕ)^129*50000000000000^97 ≤ 2225755806669^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963299781 10000000000 2225755806669 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34851131/78125000 : ℝ)^129 ≤ (8545035191599/25000000000000 : ℝ)^97 := by
    have hnat : (34851131 : ℕ)^129*25000000000000^97 ≤ 8545035191599^97*78125000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34851131 78125000 8545035191599 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6927034679/10000000000 : ℝ)^129 ≤ (15342086901271/25000000000000 : ℝ)^97 := by
    have hnat : (6927034679 : ℕ)^129*25000000000000^97 ≤ 15342086901271^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6927034679 10000000000 15342086901271 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(963299781/10000000000 : ℝ), (-34851131/78125000 : ℝ), (6927034679/10000000000 : ℝ)] ![(2225755806669/50000000000000 : ℝ), (8545035191599/25000000000000 : ℝ), (15342086901271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(963299781/10000000000 : ℝ)|^129 ≤ (2225755806669/50000000000000 : ℝ)^97
        have hw : |(963299781/10000000000 : ℝ)|=(963299781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34851131/78125000 : ℝ)|^129 ≤ (8545035191599/25000000000000 : ℝ)^97
        have hw : |(-34851131/78125000 : ℝ)|=(34851131/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6927034679/10000000000 : ℝ)|^129 ≤ (15342086901271/25000000000000 : ℝ)^97
        have hw : |(6927034679/10000000000 : ℝ)|=(6927034679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_10 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (481646891/5000000000 : ℝ)*x 0 + (1385404353/2000000000 : ℝ)*x 1 + (-2230481659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481646891/5000000000 : ℝ)^129 ≤ (556434343243/12500000000000 : ℝ)^97 := by
    have hnat : (481646891 : ℕ)^129*12500000000000^97 ≤ 556434343243^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481646891 5000000000 556434343243 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385404353/2000000000 : ℝ)^129 ≤ (2454727818151/4000000000000 : ℝ)^97 := by
    have hnat : (1385404353 : ℕ)^129*4000000000000^97 ≤ 2454727818151^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385404353 2000000000 2454727818151 4000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230481659/5000000000 : ℝ)^129 ≤ (34180329787019/100000000000000 : ℝ)^97 := by
    have hnat : (2230481659 : ℕ)^129*100000000000000^97 ≤ 34180329787019^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230481659 5000000000 34180329787019 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(481646891/5000000000 : ℝ), (1385404353/2000000000 : ℝ), (-2230481659/5000000000 : ℝ)] ![(556434343243/12500000000000 : ℝ), (2454727818151/4000000000000 : ℝ), (34180329787019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(481646891/5000000000 : ℝ)|^129 ≤ (556434343243/12500000000000 : ℝ)^97
        have hw : |(481646891/5000000000 : ℝ)|=(481646891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1385404353/2000000000 : ℝ)|^129 ≤ (2454727818151/4000000000000 : ℝ)^97
        have hw : |(1385404353/2000000000 : ℝ)|=(1385404353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230481659/5000000000 : ℝ)|^129 ≤ (34180329787019/100000000000000 : ℝ)^97
        have hw : |(-2230481659/5000000000 : ℝ)|=(2230481659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s1_11 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (962734873/5000000000 : ℝ)*x 0 + (2915608891/5000000000 : ℝ)*x 1 + (313866097/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962734873/5000000000 : ℝ)^129 ≤ (2236338624177/20000000000000 : ℝ)^97 := by
    have hnat : (962734873 : ℕ)^129*20000000000000^97 ≤ 2236338624177^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962734873 5000000000 2236338624177 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2915608891/5000000000 : ℝ)^129 ≤ (48807208195133/100000000000000 : ℝ)^97 := by
    have hnat : (2915608891 : ℕ)^129*100000000000000^97 ≤ 48807208195133^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2915608891 5000000000 48807208195133 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313866097/625000000 : ℝ)^129 ≤ (20005549330557/50000000000000 : ℝ)^97 := by
    have hnat : (313866097 : ℕ)^129*50000000000000^97 ≤ 20005549330557^97*625000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313866097 625000000 20005549330557 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(962734873/5000000000 : ℝ), (2915608891/5000000000 : ℝ), (313866097/625000000 : ℝ)] ![(2236338624177/20000000000000 : ℝ), (48807208195133/100000000000000 : ℝ), (20005549330557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(962734873/5000000000 : ℝ)|^129 ≤ (2236338624177/20000000000000 : ℝ)^97
        have hw : |(962734873/5000000000 : ℝ)|=(962734873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2915608891/5000000000 : ℝ)|^129 ≤ (48807208195133/100000000000000 : ℝ)^97
        have hw : |(2915608891/5000000000 : ℝ)|=(2915608891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313866097/625000000 : ℝ)|^129 ≤ (20005549330557/50000000000000 : ℝ)^97
        have hw : |(313866097/625000000 : ℝ)|=(313866097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1063_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1039/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4161/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (21/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (21/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (21/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (21/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (21/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (21/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (21/25000 : ℝ) ^ (8255/2048 : ℝ) ≤ (8008159/20000000000000000000 : ℝ) := by
    have hpowers : (21/25000 : ℝ)^8255 ≤ (8008159/20000000000000000000 : ℝ)^2048 := by
      have hnat : (21 : ℕ)^8255*20000000000000000000^2048 ≤ 8008159^2048*25000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21 25000 8008159 20000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21/25000 : ℝ)) (X := (8008159/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28121/100000 : ℝ) ^ (8255/2048 : ℝ) ≤ (601415034754009929/100000000000000000000 : ℝ) := by
    have hpowers : (28121/100000 : ℝ)^8255 ≤ (601415034754009929/100000000000000000000 : ℝ)^2048 := by
      have hnat : (28121 : ℕ)^8255*100000000000000000000^2048 ≤ 601415034754009929^2048*100000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28121 100000 601415034754009929 100000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28121/100000 : ℝ)) (X := (601415034754009929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000000008008159/10000000000000000000 : ℝ) ≤ (10000000000001987/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (10000000000008008159/10000000000000000000 : ℝ)^2048 ≤ (10000000000001987/10000000000000000 : ℝ)^8255 := by
      have hnat : (10000000000008008159 : ℕ)^2048*10000000000000000^8255 ≤ 10000000000001987^8255*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000000008008159 10000000000000000000 10000000000001987 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000001987/10000000000000000 : ℝ)) (X := (10000000000008008159/10000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25150353758698512681/25000000000000000000 : ℝ) ≤ (400595480464629/400000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (25150353758698512681/25000000000000000000 : ℝ)^2048 ≤ (400595480464629/400000000000000 : ℝ)^8255 := by
      have hnat : (25150353758698512681 : ℕ)^2048*400000000000000^8255 ≤ 400595480464629^8255*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25150353758698512681 25000000000000000000 400595480464629 400000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400595480464629/400000000000000 : ℝ)) (X := (25150353758698512681/25000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50601415034754009929/50000000000000000000 : ℝ) ≤ (10029774023229463/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50601415034754009929/50000000000000000000 : ℝ)^2048 ≤ (10029774023229463/10000000000000000 : ℝ)^8255 := by
      have hnat : (50601415034754009929 : ℕ)^2048*10000000000000000^8255 ≤ 10029774023229463^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50601415034754009929 50000000000000000000 10029774023229463 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029774023229463/10000000000000000 : ℝ)) (X := (50601415034754009929/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8008159/20000000000000000000 : ℝ) ≤ ((56073499796420920307/56074000000000000000 : ℝ)+2*(7443505806869/1401850000000000 : ℝ)*(21/25000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (56073499796420920307/56074000000000000000 : ℝ)+2*(7443505806869/1401850000000000 : ℝ)*(21/25000 : ℝ)=(10000000000001987/10000000000000000 : ℝ) by norm_num, show 1+2*(8008159/20000000000000000000 : ℝ)=(10000000000008008159/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(601415034754009929/100000000000000000000 : ℝ)+(8008159/20000000000000000000 : ℝ) ≤ ((56073499796420920307/56074000000000000000 : ℝ)+(7443505806869/1401850000000000 : ℝ)*((28121/100000 : ℝ)+(21/25000 : ℝ)))^(8255/2048 : ℝ) := by
    rw [show (56073499796420920307/56074000000000000000 : ℝ)+(7443505806869/1401850000000000 : ℝ)*((28121/100000 : ℝ)+(21/25000 : ℝ))=(400595480464629/400000000000000 : ℝ) by norm_num, show 1+(601415034754009929/100000000000000000000 : ℝ)+(8008159/20000000000000000000 : ℝ)=(25150353758698512681/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(601415034754009929/100000000000000000000 : ℝ) ≤ ((56073499796420920307/56074000000000000000 : ℝ)+2*(7443505806869/1401850000000000 : ℝ)*(28121/100000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (56073499796420920307/56074000000000000000 : ℝ)+2*(7443505806869/1401850000000000 : ℝ)*(28121/100000 : ℝ)=(10029774023229463/10000000000000000 : ℝ) by norm_num, show 1+2*(601415034754009929/100000000000000000000 : ℝ)=(50601415034754009929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56073499796420920307/56074000000000000000 : ℝ)*(X 1 0+X 2 0)+(7443505806869/1401850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (21/25000 : ℝ)) (hi := (28121/100000 : ℝ)) (c := (56073499796420920307/56074000000000000000 : ℝ)) (alpha := (7443505806869/1401850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56073499796420920307/56074000000000000000 : ℝ)*(X 0 1+X 2 1)+(7443505806869/1401850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (21/25000 : ℝ)) (hi := (28121/100000 : ℝ)) (c := (56073499796420920307/56074000000000000000 : ℝ)) (alpha := (7443505806869/1401850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56073499796420920307/56074000000000000000 : ℝ)*(X 0 2+X 1 2)+(7443505806869/1401850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (21/25000 : ℝ)) (hi := (28121/100000 : ℝ)) (c := (56073499796420920307/56074000000000000000 : ℝ)) (alpha := (7443505806869/1401850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85096517/400000000 : ℝ)*X 0 0+(357697763/625000000 : ℝ)*X 0 1+(2492648803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((677934871/1250000000 : ℝ)*X 1 0+(-1263626743/5000000000 : ℝ)*X 1 1+(623162241/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711739757/5000000000 : ℝ)*X 2 0+(4985297301/10000000000 : ℝ)*X 2 1+(-2527253569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((864810099/2000000000 : ℝ)*X 0 0+(732392301/2000000000 : ℝ)*X 0 1+(510721473/1000000000 : ℝ)*X 0 2+(864810099/2000000000 : ℝ)*X 1 0+(732392301/2000000000 : ℝ)*X 1 1+(510721473/1000000000 : ℝ)*X 1 2+(864810099/2000000000 : ℝ)*X 2 0+(732392301/2000000000 : ℝ)*X 2 1+(510721473/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2128339757/10000000000 : ℝ)*X 0 0+(4995678907/10000000000 : ℝ)*X 0 1+(2856284827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2617534383/5000000000 : ℝ)*X 1 0+(-1799979643/10000000000 : ℝ)*X 1 1+(2856285647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1308766687/2500000000 : ℝ)*X 2 0+(71407169/125000000 : ℝ)*X 2 1+(-359995851/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432586201/1000000000 : ℝ)*X 0 0+(2034751/4000000 : ℝ)*X 0 1+(29461677/80000000 : ℝ)*X 0 2+(432586201/1000000000 : ℝ)*X 1 0+(2034751/4000000 : ℝ)*X 1 1+(29461677/80000000 : ℝ)*X 1 2+(432586201/1000000000 : ℝ)*X 2 0+(2034751/4000000 : ℝ)*X 2 1+(29461677/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((2210399/2500000000 : ℝ)*X 0 0+(1372456191/2500000000 : ℝ)*X 0 1+(6374618123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((963299781/10000000000 : ℝ)*X 1 0+(-34851131/78125000 : ℝ)*X 1 1+(6927034679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((481646891/5000000000 : ℝ)*X 2 0+(1385404353/2000000000 : ℝ)*X 2 1+(-2230481659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((962734873/5000000000 : ℝ)*X 0 0+(2915608891/5000000000 : ℝ)*X 0 1+(313866097/625000000 : ℝ)*X 0 2+(962734873/5000000000 : ℝ)*X 1 0+(2915608891/5000000000 : ℝ)*X 1 1+(313866097/625000000 : ℝ)*X 1 2+(962734873/5000000000 : ℝ)*X 2 0+(2915608891/5000000000 : ℝ)*X 2 1+(313866097/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44203915924090494748056106473/2803700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1023594366194513/100000000000000 : ℝ)*(major0) + (1023594366194513/100000000000000 : ℝ)*(major1) + (1023594366194513/100000000000000 : ℝ)*(major2) + (1355261823552149/100000000000000 : ℝ)*(sp0) + (84703919373401/6250000000000 : ℝ)*(sp1) + (677630955595087/50000000000000 : ℝ)*(sp2) + (43245079571197/6250000000000 : ℝ)*(sp3) + (852348061/50000000000000 : ℝ)*(sp4) + (661590839/50000000000000 : ℝ)*(sp5) + (123998469/6250000000000 : ℝ)*(sp6) + (371760341/25000000000000 : ℝ)*(sp8) + (49106677/5000000000000 : ℝ)*(sp9) + (1120123957/100000000000000 : ℝ)*(sp10) + (1918417609/100000000000000 : ℝ)*(sp11) + (691923191556761/100000000000000 : ℝ)*(f.failure) + (677632507644817/50000000000000 : ℝ)*(f.sum) + (85650122590579/140185000000000000000000000000 : ℝ)*base65 + (7567557812650444509/5607400000000000000000000000000000 : ℝ)*base68 + (7719699146441244509/5607400000000000000000000000000000 : ℝ)*base70 + (3791477183555491/5607400000000000000000000000000000 : ℝ)*base71 + (282361160016393/70092500000000000000000000000 : ℝ)*base74 + (18989366557382355491/5607400000000000000000000000000000 : ℝ)*base75 + (8414402029608844509/5607400000000000000000000000000000 : ℝ)*base78 + (1836676231096244509/5607400000000000000000000000000000 : ℝ)*base80 + (92114633545733/70092500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (31928241/10000000000000000000000 : ℝ)*base89 + (31928241/10000000000000000000000 : ℝ)*base91 + (31928241/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1807047810283314842458373613/350462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34190603/25000000000000 : ℝ)*(lower4) + (263384964076353/25000000000000 : ℝ)*(major0) + (263384964076353/25000000000000 : ℝ)*(major1) + (263384964076353/25000000000000 : ℝ)*(major2) + (1598380327/100000000000000 : ℝ)*(sp0) + (539634979/25000000000000 : ℝ)*(sp1) + (4882044239/100000000000000 : ℝ)*(sp2) + (174363642055821/12500000000000 : ℝ)*(sp4) + (348727899708067/25000000000000 : ℝ)*(sp5) + (174363636751383/12500000000000 : ℝ)*(sp6) + (356082055039183/50000000000000 : ℝ)*(sp7) + (405153551/12500000000000 : ℝ)*(sp8) + (109341559/50000000000000 : ℝ)*(sp9) + (1454604477/100000000000000 : ℝ)*(sp11) + (712165564682843/100000000000000 : ℝ)*(f.failure) + (697456988027651/50000000000000 : ℝ)*(f.sum) + (298519673295459/140185000000000000000000000000 : ℝ)*base66 + (4784397083621819629/1401850000000000000000000000000000 : ℝ)*base68 + (4503841974936719629/1401850000000000000000000000000000 : ℝ)*base70 + (5017112199400119629/1401850000000000000000000000000000 : ℝ)*base72 + (175448053807297/70092500000000000000000000000 : ℝ)*base74 + (5173724159446880371/1401850000000000000000000000000000 : ℝ)*base75 + (4704071501980519629/1401850000000000000000000000000000 : ℝ)*base78 + (4610779804554569629/1401850000000000000000000000000000 : ℝ)*base80 + (49733577832601/140185000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (45378083/10000000000000000000000 : ℝ)*base89 + (45378083/10000000000000000000000 : ℝ)*base91 + (45378083/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1063_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1039/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4161/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1063_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1063_s2_0 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-218500837/1000000000 : ℝ)*x 0 + (690815833/1250000000 : ℝ)*x 1 + (2572698283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218500837/1000000000 : ℝ)^129 ≤ (3307354411951/25000000000000 : ℝ)^97 := by
    have hnat : (218500837 : ℕ)^129*25000000000000^97 ≤ 3307354411951^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218500837 1000000000 3307354411951 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (690815833/1250000000 : ℝ)^129 ≤ (45445205335091/100000000000000 : ℝ)^97 := by
    have hnat : (690815833 : ℕ)^129*100000000000000^97 ≤ 45445205335091^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690815833 1250000000 45445205335091 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2572698283/5000000000 : ℝ)^129 ≤ (41325377002441/100000000000000 : ℝ)^97 := by
    have hnat : (2572698283 : ℕ)^129*100000000000000^97 ≤ 41325377002441^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572698283 5000000000 41325377002441 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218500837/1000000000 : ℝ), (690815833/1250000000 : ℝ), (2572698283/5000000000 : ℝ)] ![(3307354411951/25000000000000 : ℝ), (45445205335091/100000000000000 : ℝ), (41325377002441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218500837/1000000000 : ℝ)|^129 ≤ (3307354411951/25000000000000 : ℝ)^97
        have hw : |(-218500837/1000000000 : ℝ)|=(218500837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(690815833/1250000000 : ℝ)|^129 ≤ (45445205335091/100000000000000 : ℝ)^97
        have hw : |(690815833/1250000000 : ℝ)|=(690815833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2572698283/5000000000 : ℝ)|^129 ≤ (41325377002441/100000000000000 : ℝ)^97
        have hw : |(2572698283/5000000000 : ℝ)|=(2572698283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s2_1 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5377337177/10000000000 : ℝ)*x 0 + (-2383796009/10000000000 : ℝ)*x 1 + (1286349483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377337177/10000000000 : ℝ)^129 ≤ (10955249001461/25000000000000 : ℝ)^97 := by
    have hnat : (5377337177 : ℕ)^129*25000000000000^97 ≤ 10955249001461^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377337177 10000000000 10955249001461 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2383796009/10000000000 : ℝ)^129 ≤ (14853612385941/100000000000000 : ℝ)^97 := by
    have hnat : (2383796009 : ℕ)^129*100000000000000^97 ≤ 14853612385941^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383796009 10000000000 14853612385941 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286349483/2500000000 : ℝ)^129 ≤ (41325391592823/100000000000000 : ℝ)^97 := by
    have hnat : (1286349483 : ℕ)^129*100000000000000^97 ≤ 41325391592823^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286349483 2500000000 41325391592823 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377337177/10000000000 : ℝ), (-2383796009/10000000000 : ℝ), (1286349483/2500000000 : ℝ)] ![(10955249001461/25000000000000 : ℝ), (14853612385941/100000000000000 : ℝ), (41325391592823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377337177/10000000000 : ℝ)|^129 ≤ (10955249001461/25000000000000 : ℝ)^97
        have hw : |(5377337177/10000000000 : ℝ)|=(5377337177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2383796009/10000000000 : ℝ)|^129 ≤ (14853612385941/100000000000000 : ℝ)^97
        have hw : |(-2383796009/10000000000 : ℝ)|=(2383796009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1286349483/2500000000 : ℝ)|^129 ≤ (41325391592823/100000000000000 : ℝ)^97
        have hw : |(1286349483/2500000000 : ℝ)|=(1286349483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s2_2 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (215093493/400000000 : ℝ)*x 0 + (1286349437/2500000000 : ℝ)*x 1 + (-2383796053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215093493/400000000 : ℝ)^129 ≤ (2738812350613/6250000000000 : ℝ)^97 := by
    have hnat : (215093493 : ℕ)^129*6250000000000^97 ≤ 2738812350613^97*400000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215093493 400000000 2738812350613 6250000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286349437/2500000000 : ℝ)^129 ≤ (41325389627501/100000000000000 : ℝ)^97 := by
    have hnat : (1286349437 : ℕ)^129*100000000000000^97 ≤ 41325389627501^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286349437 2500000000 41325389627501 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2383796053/10000000000 : ℝ)^129 ≤ (2970722550111/20000000000000 : ℝ)^97 := by
    have hnat : (2383796053 : ℕ)^129*20000000000000^97 ≤ 2970722550111^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383796053 10000000000 2970722550111 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215093493/400000000 : ℝ), (1286349437/2500000000 : ℝ), (-2383796053/10000000000 : ℝ)] ![(2738812350613/6250000000000 : ℝ), (41325389627501/100000000000000 : ℝ), (2970722550111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215093493/400000000 : ℝ)|^129 ≤ (2738812350613/6250000000000 : ℝ)^97
        have hw : |(215093493/400000000 : ℝ)|=(215093493/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1286349437/2500000000 : ℝ)|^129 ≤ (41325389627501/100000000000000 : ℝ)^97
        have hw : |(1286349437/2500000000 : ℝ)|=(1286349437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2383796053/10000000000 : ℝ)|^129 ≤ (2970722550111/20000000000000 : ℝ)^97
        have hw : |(-2383796053/10000000000 : ℝ)|=(2383796053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s2_3 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (545417611/1250000000 : ℝ)*x 0 + (2003097181/5000000000 : ℝ)*x 1 + (4752703061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545417611/1250000000 : ℝ)^129 ≤ (3318918540781/10000000000000 : ℝ)^97 := by
    have hnat : (545417611 : ℕ)^129*10000000000000^97 ≤ 3318918540781^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545417611 1250000000 3318918540781 10000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003097181/5000000000 : ℝ)^129 ≤ (29626103517099/100000000000000 : ℝ)^97 := by
    have hnat : (2003097181 : ℕ)^129*100000000000000^97 ≤ 29626103517099^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003097181 5000000000 29626103517099 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4752703061/10000000000 : ℝ)^129 ≤ (37184711064547/100000000000000 : ℝ)^97 := by
    have hnat : (4752703061 : ℕ)^129*100000000000000^97 ≤ 37184711064547^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752703061 10000000000 37184711064547 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545417611/1250000000 : ℝ), (2003097181/5000000000 : ℝ), (4752703061/10000000000 : ℝ)] ![(3318918540781/10000000000000 : ℝ), (29626103517099/100000000000000 : ℝ), (37184711064547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545417611/1250000000 : ℝ)|^129 ≤ (3318918540781/10000000000000 : ℝ)^97
        have hw : |(545417611/1250000000 : ℝ)|=(545417611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2003097181/5000000000 : ℝ)|^129 ≤ (29626103517099/100000000000000 : ℝ)^97
        have hw : |(2003097181/5000000000 : ℝ)|=(2003097181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4752703061/10000000000 : ℝ)|^129 ≤ (37184711064547/100000000000000 : ℝ)^97
        have hw : |(4752703061/10000000000 : ℝ)|=(4752703061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s2_4 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092567509/5000000000 : ℝ)*x 0 + (1029635277/2000000000 : ℝ)*x 1 + (138092947/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092567509/5000000000 : ℝ)^129 ≤ (13230437431551/100000000000000 : ℝ)^97 := by
    have hnat : (1092567509 : ℕ)^129*100000000000000^97 ≤ 13230437431551^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092567509 5000000000 13230437431551 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029635277/2000000000 : ℝ)^129 ≤ (20677535585253/50000000000000 : ℝ)^97 := by
    have hnat : (1029635277 : ℕ)^129*50000000000000^97 ≤ 20677535585253^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029635277 2000000000 20677535585253 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138092947/250000000 : ℝ)^129 ≤ (22707245691409/50000000000000 : ℝ)^97 := by
    have hnat : (138092947 : ℕ)^129*50000000000000^97 ≤ 22707245691409^97*250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138092947 250000000 22707245691409 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092567509/5000000000 : ℝ), (1029635277/2000000000 : ℝ), (138092947/250000000 : ℝ)] ![(13230437431551/100000000000000 : ℝ), (20677535585253/50000000000000 : ℝ), (22707245691409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092567509/5000000000 : ℝ)|^129 ≤ (13230437431551/100000000000000 : ℝ)^97
        have hw : |(-1092567509/5000000000 : ℝ)|=(1092567509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029635277/2000000000 : ℝ)|^129 ≤ (20677535585253/50000000000000 : ℝ)^97
        have hw : |(1029635277/2000000000 : ℝ)|=(1029635277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138092947/250000000 : ℝ)|^129 ≤ (22707245691409/50000000000000 : ℝ)^97
        have hw : |(138092947/250000000 : ℝ)|=(138092947/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s2_5 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5281156531/10000000000 : ℝ)*x 0 + (-1002738591/5000000000 : ℝ)*x 1 + (2761858981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281156531/10000000000 : ℝ)^129 ≤ (8556343345651/20000000000000 : ℝ)^97 := by
    have hnat : (5281156531 : ℕ)^129*20000000000000^97 ≤ 8556343345651^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281156531 10000000000 8556343345651 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002738591/5000000000 : ℝ)^129 ≤ (11803790983201/100000000000000 : ℝ)^97 := by
    have hnat : (1002738591 : ℕ)^129*100000000000000^97 ≤ 11803790983201^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002738591 5000000000 11803790983201 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2761858981/5000000000 : ℝ)^129 ≤ (4541449227941/10000000000000 : ℝ)^97 := by
    have hnat : (2761858981 : ℕ)^129*10000000000000^97 ≤ 4541449227941^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761858981 5000000000 4541449227941 10000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281156531/10000000000 : ℝ), (-1002738591/5000000000 : ℝ), (2761858981/5000000000 : ℝ)] ![(8556343345651/20000000000000 : ℝ), (11803790983201/100000000000000 : ℝ), (4541449227941/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281156531/10000000000 : ℝ)|^129 ≤ (8556343345651/20000000000000 : ℝ)^97
        have hw : |(5281156531/10000000000 : ℝ)|=(5281156531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002738591/5000000000 : ℝ)|^129 ≤ (11803790983201/100000000000000 : ℝ)^97
        have hw : |(-1002738591/5000000000 : ℝ)|=(1002738591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2761858981/5000000000 : ℝ)|^129 ≤ (4541449227941/10000000000000 : ℝ)^97
        have hw : |(2761858981/5000000000 : ℝ)|=(2761858981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s2_6 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2640578387/5000000000 : ℝ)*x 0 + (5523717797/10000000000 : ℝ)*x 1 + (-2005477077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640578387/5000000000 : ℝ)^129 ≤ (42781719346157/100000000000000 : ℝ)^97 := by
    have hnat : (2640578387 : ℕ)^129*100000000000000^97 ≤ 42781719346157^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640578387 5000000000 42781719346157 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5523717797/10000000000 : ℝ)^129 ≤ (11353622618823/25000000000000 : ℝ)^97 := by
    have hnat : (5523717797 : ℕ)^129*25000000000000^97 ≤ 11353622618823^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523717797 10000000000 11353622618823 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005477077/10000000000 : ℝ)^129 ≤ (2950947540329/25000000000000 : ℝ)^97 := by
    have hnat : (2005477077 : ℕ)^129*25000000000000^97 ≤ 2950947540329^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005477077 10000000000 2950947540329 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640578387/5000000000 : ℝ), (5523717797/10000000000 : ℝ), (-2005477077/10000000000 : ℝ)] ![(42781719346157/100000000000000 : ℝ), (11353622618823/25000000000000 : ℝ), (2950947540329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640578387/5000000000 : ℝ)|^129 ≤ (42781719346157/100000000000000 : ℝ)^97
        have hw : |(2640578387/5000000000 : ℝ)|=(2640578387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5523717797/10000000000 : ℝ)|^129 ≤ (11353622618823/25000000000000 : ℝ)^97
        have hw : |(5523717797/10000000000 : ℝ)|=(5523717797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2005477077/10000000000 : ℝ)|^129 ≤ (2950947540329/25000000000000 : ℝ)^97
        have hw : |(-2005477077/10000000000 : ℝ)|=(2005477077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s2_7 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4363587747/10000000000 : ℝ)*x 0 + (2373631903/5000000000 : ℝ)*x 1 + (1002923197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363587747/10000000000 : ℝ)^129 ≤ (6638336515947/20000000000000 : ℝ)^97 := by
    have hnat : (4363587747 : ℕ)^129*20000000000000^97 ≤ 6638336515947^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363587747 10000000000 6638336515947 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2373631903/5000000000 : ℝ)^129 ≤ (37128126352199/100000000000000 : ℝ)^97 := by
    have hnat : (2373631903 : ℕ)^129*100000000000000^97 ≤ 37128126352199^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373631903 5000000000 37128126352199 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002923197/2500000000 : ℝ)^129 ≤ (14840095524179/50000000000000 : ℝ)^97 := by
    have hnat : (1002923197 : ℕ)^129*50000000000000^97 ≤ 14840095524179^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002923197 2500000000 14840095524179 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363587747/10000000000 : ℝ), (2373631903/5000000000 : ℝ), (1002923197/2500000000 : ℝ)] ![(6638336515947/20000000000000 : ℝ), (37128126352199/100000000000000 : ℝ), (14840095524179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363587747/10000000000 : ℝ)|^129 ≤ (6638336515947/20000000000000 : ℝ)^97
        have hw : |(4363587747/10000000000 : ℝ)|=(4363587747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2373631903/5000000000 : ℝ)|^129 ≤ (37128126352199/100000000000000 : ℝ)^97
        have hw : |(2373631903/5000000000 : ℝ)|=(2373631903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002923197/2500000000 : ℝ)|^129 ≤ (14840095524179/50000000000000 : ℝ)^97
        have hw : |(1002923197/2500000000 : ℝ)|=(1002923197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1063_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4161/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1039/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8697/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4161/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1039/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4161/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1039/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4161/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1039/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4161/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1039/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4161/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1039/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4161/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1039/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1039/20000 : ℝ) ^ (8255/2048 : ℝ) ≤ (665014954449693/100000000000000000000 : ℝ) := by
    have hpowers : (1039/20000 : ℝ)^8255 ≤ (665014954449693/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1039 : ℕ)^8255*100000000000000000000^2048 ≤ 665014954449693^2048*20000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1039 20000 665014954449693 100000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1039/20000 : ℝ)) (X := (665014954449693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4161/20000 : ℝ) ^ (8255/2048 : ℝ) ≤ (178523974772593009/100000000000000000000 : ℝ) := by
    have hpowers : (4161/20000 : ℝ)^8255 ≤ (178523974772593009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4161 : ℕ)^8255*100000000000000000000^2048 ≤ 178523974772593009^2048*20000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4161 20000 178523974772593009 100000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4161/20000 : ℝ)) (X := (178523974772593009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000665014954449693/50000000000000000000 : ℝ) ≤ (10000032996821723/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50000665014954449693/50000000000000000000 : ℝ)^2048 ≤ (10000032996821723/10000000000000000 : ℝ)^8255 := by
      have hnat : (50000665014954449693 : ℕ)^2048*10000000000000000^8255 ≤ 10000032996821723^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000665014954449693 50000000000000000000 10000032996821723 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000032996821723/10000000000000000 : ℝ)) (X := (50000665014954449693/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50089594494863521351/50000000000000000000 : ℝ) ≤ (500222127248487/500000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50089594494863521351/50000000000000000000 : ℝ)^2048 ≤ (500222127248487/500000000000000 : ℝ)^8255 := by
      have hnat : (50089594494863521351 : ℕ)^2048*500000000000000^8255 ≤ 500222127248487^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50089594494863521351 50000000000000000000 500222127248487 500000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500222127248487/500000000000000 : ℝ)) (X := (50089594494863521351/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50178523974772593009/50000000000000000000 : ℝ) ≤ (10008852093117757/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50178523974772593009/50000000000000000000 : ℝ)^2048 ≤ (10008852093117757/10000000000000000 : ℝ)^8255 := by
      have hnat : (50178523974772593009 : ℕ)^2048*10000000000000000^8255 ≤ 10008852093117757^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50178523974772593009 50000000000000000000 10008852093117757 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008852093117757/10000000000000000 : ℝ)) (X := (50178523974772593009/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(665014954449693/100000000000000000000 : ℝ) ≤ ((780273499375645997/780500000000000000 : ℝ)+2*(4409548148017/1561000000000000 : ℝ)*(1039/20000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (780273499375645997/780500000000000000 : ℝ)+2*(4409548148017/1561000000000000 : ℝ)*(1039/20000 : ℝ)=(10000032996821723/10000000000000000 : ℝ) by norm_num, show 1+2*(665014954449693/100000000000000000000 : ℝ)=(50000665014954449693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(178523974772593009/100000000000000000000 : ℝ)+(665014954449693/100000000000000000000 : ℝ) ≤ ((780273499375645997/780500000000000000 : ℝ)+(4409548148017/1561000000000000 : ℝ)*((4161/20000 : ℝ)+(1039/20000 : ℝ)))^(8255/2048 : ℝ) := by
    rw [show (780273499375645997/780500000000000000 : ℝ)+(4409548148017/1561000000000000 : ℝ)*((4161/20000 : ℝ)+(1039/20000 : ℝ))=(500222127248487/500000000000000 : ℝ) by norm_num, show 1+(178523974772593009/100000000000000000000 : ℝ)+(665014954449693/100000000000000000000 : ℝ)=(50089594494863521351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(178523974772593009/100000000000000000000 : ℝ) ≤ ((780273499375645997/780500000000000000 : ℝ)+2*(4409548148017/1561000000000000 : ℝ)*(4161/20000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (780273499375645997/780500000000000000 : ℝ)+2*(4409548148017/1561000000000000 : ℝ)*(4161/20000 : ℝ)=(10008852093117757/10000000000000000 : ℝ) by norm_num, show 1+2*(178523974772593009/100000000000000000000 : ℝ)=(50178523974772593009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (780273499375645997/780500000000000000 : ℝ)*(X 1 0+X 2 0)+(4409548148017/1561000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (1039/20000 : ℝ)) (hi := (4161/20000 : ℝ)) (c := (780273499375645997/780500000000000000 : ℝ)) (alpha := (4409548148017/1561000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (780273499375645997/780500000000000000 : ℝ)*(X 0 1+X 2 1)+(4409548148017/1561000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (1039/20000 : ℝ)) (hi := (4161/20000 : ℝ)) (c := (780273499375645997/780500000000000000 : ℝ)) (alpha := (4409548148017/1561000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (780273499375645997/780500000000000000 : ℝ)*(X 0 2+X 1 2)+(4409548148017/1561000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (1039/20000 : ℝ)) (hi := (4161/20000 : ℝ)) (c := (780273499375645997/780500000000000000 : ℝ)) (alpha := (4409548148017/1561000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-218500837/1000000000 : ℝ)*X 0 0+(690815833/1250000000 : ℝ)*X 0 1+(2572698283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377337177/10000000000 : ℝ)*X 1 0+(-2383796009/10000000000 : ℝ)*X 1 1+(1286349483/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((215093493/400000000 : ℝ)*X 2 0+(1286349437/2500000000 : ℝ)*X 2 1+(-2383796053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545417611/1250000000 : ℝ)*X 0 0+(2003097181/5000000000 : ℝ)*X 0 1+(4752703061/10000000000 : ℝ)*X 0 2+(545417611/1250000000 : ℝ)*X 1 0+(2003097181/5000000000 : ℝ)*X 1 1+(4752703061/10000000000 : ℝ)*X 1 2+(545417611/1250000000 : ℝ)*X 2 0+(2003097181/5000000000 : ℝ)*X 2 1+(4752703061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1092567509/5000000000 : ℝ)*X 0 0+(1029635277/2000000000 : ℝ)*X 0 1+(138092947/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281156531/10000000000 : ℝ)*X 1 0+(-1002738591/5000000000 : ℝ)*X 1 1+(2761858981/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640578387/5000000000 : ℝ)*X 2 0+(5523717797/10000000000 : ℝ)*X 2 1+(-2005477077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363587747/10000000000 : ℝ)*X 0 0+(2373631903/5000000000 : ℝ)*X 0 1+(1002923197/2500000000 : ℝ)*X 0 2+(4363587747/10000000000 : ℝ)*X 1 0+(2373631903/5000000000 : ℝ)*X 1 1+(1002923197/2500000000 : ℝ)*X 1 2+(4363587747/10000000000 : ℝ)*X 2 0+(2373631903/5000000000 : ℝ)*X 2 1+(1002923197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8260948529167404153018171/9756250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115712459/50000000000000 : ℝ)*(base1) + (443892669/20000000000000 : ℝ)*(base19) + (2291678833/100000000000000 : ℝ)*(base23) + (213197791/100000000000000 : ℝ)*(upper3) + (40732643/20000000000000 : ℝ)*(upper5) + (495427134723173/25000000000000 : ℝ)*(major0) + (495427134723173/25000000000000 : ℝ)*(major1) + (495427134723173/25000000000000 : ℝ)*(major2) + (1311902318017987/50000000000000 : ℝ)*(sp0) + (2623831356163759/100000000000000 : ℝ)*(sp1) + (2623831283948271/100000000000000 : ℝ)*(sp2) + (83723501617821/6250000000000 : ℝ)*(sp3) + (29171016047/100000000000000 : ℝ)*(sp4) + (7216623751/100000000000000 : ℝ)*(sp7) + (334895868483451/25000000000000 : ℝ)*(f.failure) + (81994799238347/3125000000000 : ℝ)*(f.sum) + (99415132686407/39025000000000000000000000000 : ℝ)*base65 + (108617966139446481/19512500000000000000000000000000 : ℝ)*base67 + (81730241459458981/19512500000000000000000000000000 : ℝ)*base69 + (95377413132208981/19512500000000000000000000000000 : ℝ)*base71 + (24221459319793/39025000000000000000000000000 : ℝ)*base74 + (4479068692158981/19512500000000000000000000000000 : ℝ)*base75 + (63245267524058981/19512500000000000000000000000000 : ℝ)*base77 + (168009472126983981/19512500000000000000000000000000 : ℝ)*base79 + (14130102191143/39025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (22535869/2500000000000000000000 : ℝ)*base90 + (22535869/2500000000000000000000 : ℝ)*base92 + (22535869/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11834941370254665952650129/1393750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1653879411/100000000000000 : ℝ)*(base19) + (952577687/50000000000000 : ℝ)*(base23) + (110087929/50000000000000 : ℝ)*(upper3) + (22839107/50000000000000 : ℝ)*(lower4) + (45241207/25000000000000 : ℝ)*(upper5) + (502788722738661/25000000000000 : ℝ)*(major0) + (502788722738661/25000000000000 : ℝ)*(major1) + (502788722738661/25000000000000 : ℝ)*(major2) + (14326028283/100000000000000 : ℝ)*(sp1) + (16646475147/100000000000000 : ℝ)*(sp2) + (166426316009471/6250000000000 : ℝ)*(sp4) + (1331402538121921/50000000000000 : ℝ)*(sp5) + (532560500904203/20000000000000 : ℝ)*(sp6) + (1359488442709823/100000000000000 : ℝ)*(sp7) + (1359488442709823/100000000000000 : ℝ)*(f.failure) + (166426316009471/6250000000000 : ℝ)*(f.sum) + (51378402694851/39025000000000000000000000000 : ℝ)*base66 + (3115677082816483/19512500000000000000000000000000 : ℝ)*base68 + (152996584906141483/19512500000000000000000000000000 : ℝ)*base70 + (156080101768266483/19512500000000000000000000000000 : ℝ)*base72 + (82798155673799/39025000000000000000000000000 : ℝ)*base73 + (99851112179641483/19512500000000000000000000000000 : ℝ)*base76 + (108944890989666483/19512500000000000000000000000000 : ℝ)*base78 + (11137179021703983/19512500000000000000000000000000 : ℝ)*base80 + (18062177060747/4878125000000000000000000000 : ℝ)*base82 + (41071463/10000000000000000000000 : ℝ)*base89 + (41071463/10000000000000000000000 : ℝ)*base91 + (41071463/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1063_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4161/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1039/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1063_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1063_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16751/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1063_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1063_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1063_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16751/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1063_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
