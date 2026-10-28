-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1154_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:00.616997+00:00
-- url     : https://prove2.me/submissions/082e9aa8-8a91-4c56-8353-d5c5324fc632

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
theorem support_rectangle_w1154_s0_0 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-472004633/2500000000 : ℝ)*x 0 + (6051560837/10000000000 : ℝ)*x 1 + (956397621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (472004633/2500000000 : ℝ)^8347 ≤ (10980281172463/100000000000000 : ℝ)^6299 := by
    have hnat : (472004633 : ℕ)^8347*100000000000000^6299 ≤ 10980281172463^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472004633 2500000000 10980281172463 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6051560837/10000000000 : ℝ)^8347 ≤ (25698971612869/50000000000000 : ℝ)^6299 := by
    have hnat : (6051560837 : ℕ)^8347*50000000000000^6299 ≤ 25698971612869^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6051560837 10000000000 25698971612869 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956397621/2000000000 : ℝ)^8347 ≤ (18810887793201/50000000000000 : ℝ)^6299 := by
    have hnat : (956397621 : ℕ)^8347*50000000000000^6299 ≤ 18810887793201^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956397621 2000000000 18810887793201 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-472004633/2500000000 : ℝ), (6051560837/10000000000 : ℝ), (956397621/2000000000 : ℝ)] ![(10980281172463/100000000000000 : ℝ), (25698971612869/50000000000000 : ℝ), (18810887793201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-472004633/2500000000 : ℝ)|^8347 ≤ (10980281172463/100000000000000 : ℝ)^6299
        have hw : |(-472004633/2500000000 : ℝ)|=(472004633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6051560837/10000000000 : ℝ)|^8347 ≤ (25698971612869/50000000000000 : ℝ)^6299
        have hw : |(6051560837/10000000000 : ℝ)|=(6051560837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(956397621/2000000000 : ℝ)|^8347 ≤ (18810887793201/50000000000000 : ℝ)^6299
        have hw : |(956397621/2000000000 : ℝ)|=(956397621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s0_1 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516117681/10000000000 : ℝ)*x 0 + (-261626353/1000000000 : ℝ)*x 1 + (597748511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516117681/10000000000 : ℝ)^8347 ≤ (9092024019171/20000000000000 : ℝ)^6299 := by
    have hnat : (5516117681 : ℕ)^8347*20000000000000^6299 ≤ 9092024019171^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516117681 10000000000 9092024019171 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261626353/1000000000 : ℝ)^8347 ≤ (16918104476209/100000000000000 : ℝ)^6299 := by
    have hnat : (261626353 : ℕ)^8347*100000000000000^6299 ≤ 16918104476209^6299*1000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261626353 1000000000 16918104476209 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597748511/1250000000 : ℝ)^8347 ≤ (9405443852293/25000000000000 : ℝ)^6299 := by
    have hnat : (597748511 : ℕ)^8347*25000000000000^6299 ≤ 9405443852293^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597748511 1250000000 9405443852293 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516117681/10000000000 : ℝ), (-261626353/1000000000 : ℝ), (597748511/1250000000 : ℝ)] ![(9092024019171/20000000000000 : ℝ), (16918104476209/100000000000000 : ℝ), (9405443852293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516117681/10000000000 : ℝ)|^8347 ≤ (9092024019171/20000000000000 : ℝ)^6299
        have hw : |(5516117681/10000000000 : ℝ)|=(5516117681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261626353/1000000000 : ℝ)|^8347 ≤ (16918104476209/100000000000000 : ℝ)^6299
        have hw : |(-261626353/1000000000 : ℝ)|=(261626353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597748511/1250000000 : ℝ)|^8347 ≤ (9405443852293/25000000000000 : ℝ)^6299
        have hw : |(597748511/1250000000 : ℝ)|=(597748511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s0_2 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1379029423/2500000000 : ℝ)*x 0 + (4781988109/10000000000 : ℝ)*x 1 + (-2616263491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379029423/2500000000 : ℝ)^8347 ≤ (2841257513499/6250000000000 : ℝ)^6299 := by
    have hnat : (1379029423 : ℕ)^8347*6250000000000^6299 ≤ 2841257513499^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379029423 2500000000 2841257513499 6250000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4781988109/10000000000 : ℝ)^8347 ≤ (4702721953513/12500000000000 : ℝ)^6299 := by
    have hnat : (4781988109 : ℕ)^8347*12500000000000^6299 ≤ 4702721953513^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781988109 10000000000 4702721953513 12500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616263491/10000000000 : ℝ)^8347 ≤ (8459052071009/50000000000000 : ℝ)^6299 := by
    have hnat : (2616263491 : ℕ)^8347*50000000000000^6299 ≤ 8459052071009^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616263491 10000000000 8459052071009 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379029423/2500000000 : ℝ), (4781988109/10000000000 : ℝ), (-2616263491/10000000000 : ℝ)] ![(2841257513499/6250000000000 : ℝ), (4702721953513/12500000000000 : ℝ), (8459052071009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379029423/2500000000 : ℝ)|^8347 ≤ (2841257513499/6250000000000 : ℝ)^6299
        have hw : |(1379029423/2500000000 : ℝ)|=(1379029423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4781988109/10000000000 : ℝ)|^8347 ≤ (4702721953513/12500000000000 : ℝ)^6299
        have hw : |(4781988109/10000000000 : ℝ)|=(4781988109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2616263491/10000000000 : ℝ)|^8347 ≤ (8459052071009/50000000000000 : ℝ)^6299
        have hw : |(-2616263491/10000000000 : ℝ)|=(2616263491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s0_3 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2100011007/5000000000 : ℝ)*x 0 + (3120529099/10000000000 : ℝ)*x 1 + (5652257537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100011007/5000000000 : ℝ)^8347 ≤ (15839044767423/50000000000000 : ℝ)^6299 := by
    have hnat : (2100011007 : ℕ)^8347*50000000000000^6299 ≤ 15839044767423^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100011007 5000000000 15839044767423 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120529099/10000000000 : ℝ)^8347 ≤ (267113712933/1250000000000 : ℝ)^6299 := by
    have hnat : (3120529099 : ℕ)^8347*1250000000000^6299 ≤ 267113712933^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120529099 10000000000 267113712933 1250000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5652257537/10000000000 : ℝ)^8347 ≤ (9390562684187/20000000000000 : ℝ)^6299 := by
    have hnat : (5652257537 : ℕ)^8347*20000000000000^6299 ≤ 9390562684187^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5652257537 10000000000 9390562684187 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100011007/5000000000 : ℝ), (3120529099/10000000000 : ℝ), (5652257537/10000000000 : ℝ)] ![(15839044767423/50000000000000 : ℝ), (267113712933/1250000000000 : ℝ), (9390562684187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100011007/5000000000 : ℝ)|^8347 ≤ (15839044767423/50000000000000 : ℝ)^6299
        have hw : |(2100011007/5000000000 : ℝ)|=(2100011007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120529099/10000000000 : ℝ)|^8347 ≤ (267113712933/1250000000000 : ℝ)^6299
        have hw : |(3120529099/10000000000 : ℝ)|=(3120529099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5652257537/10000000000 : ℝ)|^8347 ≤ (9390562684187/20000000000000 : ℝ)^6299
        have hw : |(5652257537/10000000000 : ℝ)|=(5652257537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s0_4 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-94656447/500000000 : ℝ)*x 0 + (4814733449/10000000000 : ℝ)*x 1 + (1504415821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94656447/500000000 : ℝ)^8347 ≤ (11019682652021/100000000000000 : ℝ)^6299 := by
    have hnat : (94656447 : ℕ)^8347*100000000000000^6299 ≤ 11019682652021^6299*500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94656447 500000000 11019682652021 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4814733449/10000000000 : ℝ)^8347 ≤ (37963535877661/100000000000000 : ℝ)^6299 := by
    have hnat : (4814733449 : ℕ)^8347*100000000000000^6299 ≤ 37963535877661^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814733449 10000000000 37963535877661 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1504415821/2500000000 : ℝ)^8347 ≤ (10203356290257/20000000000000 : ℝ)^6299 := by
    have hnat : (1504415821 : ℕ)^8347*20000000000000^6299 ≤ 10203356290257^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504415821 2500000000 10203356290257 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94656447/500000000 : ℝ), (4814733449/10000000000 : ℝ), (1504415821/2500000000 : ℝ)] ![(11019682652021/100000000000000 : ℝ), (37963535877661/100000000000000 : ℝ), (10203356290257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94656447/500000000 : ℝ)|^8347 ≤ (11019682652021/100000000000000 : ℝ)^6299
        have hw : |(-94656447/500000000 : ℝ)|=(94656447/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4814733449/10000000000 : ℝ)|^8347 ≤ (37963535877661/100000000000000 : ℝ)^6299
        have hw : |(4814733449/10000000000 : ℝ)|=(4814733449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1504415821/2500000000 : ℝ)|^8347 ≤ (10203356290257/20000000000000 : ℝ)^6299
        have hw : |(1504415821/2500000000 : ℝ)|=(1504415821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s0_5 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171087877/10000000000 : ℝ)*x 0 + (-138058853/1000000000 : ℝ)*x 1 + (6017663107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171087877/10000000000 : ℝ)^8347 ≤ (41730974698753/100000000000000 : ℝ)^6299 := by
    have hnat : (5171087877 : ℕ)^8347*100000000000000^6299 ≤ 41730974698753^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171087877 10000000000 41730974698753 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138058853/1000000000 : ℝ)^8347 ≤ (1813061458449/25000000000000 : ℝ)^6299 := by
    have hnat : (138058853 : ℕ)^8347*25000000000000^6299 ≤ 1813061458449^6299*1000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138058853 1000000000 1813061458449 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6017663107/10000000000 : ℝ)^8347 ≤ (6377097432853/12500000000000 : ℝ)^6299 := by
    have hnat : (6017663107 : ℕ)^8347*12500000000000^6299 ≤ 6377097432853^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017663107 10000000000 6377097432853 12500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171087877/10000000000 : ℝ), (-138058853/1000000000 : ℝ), (6017663107/10000000000 : ℝ)] ![(41730974698753/100000000000000 : ℝ), (1813061458449/25000000000000 : ℝ), (6377097432853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171087877/10000000000 : ℝ)|^8347 ≤ (41730974698753/100000000000000 : ℝ)^6299
        have hw : |(5171087877/10000000000 : ℝ)|=(5171087877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138058853/1000000000 : ℝ)|^8347 ≤ (1813061458449/25000000000000 : ℝ)^6299
        have hw : |(-138058853/1000000000 : ℝ)|=(138058853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6017663107/10000000000 : ℝ)|^8347 ≤ (6377097432853/12500000000000 : ℝ)^6299
        have hw : |(6017663107/10000000000 : ℝ)|=(6017663107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s0_6 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (258554393/500000000 : ℝ)*x 0 + (6017663163/10000000000 : ℝ)*x 1 + (-1380588463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258554393/500000000 : ℝ)^8347 ≤ (41730974516957/100000000000000 : ℝ)^6299 := by
    have hnat : (258554393 : ℕ)^8347*100000000000000^6299 ≤ 41730974516957^6299*500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258554393 500000000 41730974516957 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6017663163/10000000000 : ℝ)^8347 ≤ (51016780091941/100000000000000 : ℝ)^6299 := by
    have hnat : (6017663163 : ℕ)^8347*100000000000000^6299 ≤ 51016780091941^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017663163 10000000000 51016780091941 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380588463/10000000000 : ℝ)^8347 ≤ (3626122683707/50000000000000 : ℝ)^6299 := by
    have hnat : (1380588463 : ℕ)^8347*50000000000000^6299 ≤ 3626122683707^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380588463 10000000000 3626122683707 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258554393/500000000 : ℝ), (6017663163/10000000000 : ℝ), (-1380588463/10000000000 : ℝ)] ![(41730974516957/100000000000000 : ℝ), (51016780091941/100000000000000 : ℝ), (3626122683707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258554393/500000000 : ℝ)|^8347 ≤ (41730974516957/100000000000000 : ℝ)^6299
        have hw : |(258554393/500000000 : ℝ)|=(258554393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6017663163/10000000000 : ℝ)|^8347 ≤ (51016780091941/100000000000000 : ℝ)^6299
        have hw : |(6017663163/10000000000 : ℝ)|=(6017663163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1380588463/10000000000 : ℝ)|^8347 ≤ (3626122683707/50000000000000 : ℝ)^6299
        have hw : |(-1380588463/10000000000 : ℝ)|=(1380588463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s0_7 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2105106547/5000000000 : ℝ)*x 0 + (34918487/62500000 : ℝ)*x 1 + (3188126307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105106547/5000000000 : ℝ)^8347 ≤ (15889992823463/50000000000000 : ℝ)^6299 := by
    have hnat : (2105106547 : ℕ)^8347*50000000000000^6299 ≤ 15889992823463^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105106547 5000000000 15889992823463 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34918487/62500000 : ℝ)^8347 ≤ (46235365185771/100000000000000 : ℝ)^6299 := by
    have hnat : (34918487 : ℕ)^8347*100000000000000^6299 ≤ 46235365185771^6299*62500000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34918487 62500000 46235365185771 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3188126307/10000000000 : ℝ)^8347 ≤ (4396929828729/20000000000000 : ℝ)^6299 := by
    have hnat : (3188126307 : ℕ)^8347*20000000000000^6299 ≤ 4396929828729^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188126307 10000000000 4396929828729 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105106547/5000000000 : ℝ), (34918487/62500000 : ℝ), (3188126307/10000000000 : ℝ)] ![(15889992823463/50000000000000 : ℝ), (46235365185771/100000000000000 : ℝ), (4396929828729/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105106547/5000000000 : ℝ)|^8347 ≤ (15889992823463/50000000000000 : ℝ)^6299
        have hw : |(2105106547/5000000000 : ℝ)|=(2105106547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34918487/62500000 : ℝ)|^8347 ≤ (46235365185771/100000000000000 : ℝ)^6299
        have hw : |(34918487/62500000 : ℝ)|=(34918487/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3188126307/10000000000 : ℝ)|^8347 ≤ (4396929828729/20000000000000 : ℝ)^6299
        have hw : |(3188126307/10000000000 : ℝ)|=(3188126307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1154_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (463/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27769/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4173/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4173 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4173*1^1024 ≤ 0^1024*1^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4173/1024 : ℝ) ≤ (2389553409580847143/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4173 ≤ (2389553409580847143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4173*100000000000000000000^1024 ≤ 2389553409580847143^1024*5^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2389553409580847143 100000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2389553409580847143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4173 := by
      have hnat : (1 : ℕ)^1024*1^4173 ≤ 1^4173*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102389553409580847143/100000000000000000000 : ℝ) ≤ (10058115142602187/10000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (102389553409580847143/100000000000000000000 : ℝ)^1024 ≤ (10058115142602187/10000000000000000 : ℝ)^4173 := by
      have hnat : (102389553409580847143 : ℕ)^1024*10000000000000000^4173 ≤ 10058115142602187^4173*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102389553409580847143 100000000000000000000 10058115142602187 10000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058115142602187/10000000000000000 : ℝ)) (X := (102389553409580847143/100000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52389553409580847143/50000000000000000000 : ℝ) ≤ (5058115142602187/5000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (52389553409580847143/50000000000000000000 : ℝ)^1024 ≤ (5058115142602187/5000000000000000 : ℝ)^4173 := by
      have hnat : (52389553409580847143 : ℕ)^1024*5000000000000000^4173 ≤ 5058115142602187^4173*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52389553409580847143 50000000000000000000 5058115142602187 5000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058115142602187/5000000000000000 : ℝ)) (X := (52389553409580847143/50000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58115142602187/4000000000000000 : ℝ)*(0 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(58115142602187/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2389553409580847143/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58115142602187/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4173/1024 : ℝ) := by
    rw [show (1 : ℝ)+(58115142602187/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058115142602187/10000000000000000 : ℝ) by norm_num, show 1+(2389553409580847143/100000000000000000000 : ℝ)+(0 : ℝ)=(102389553409580847143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2389553409580847143/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58115142602187/4000000000000000 : ℝ)*(2/5 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(58115142602187/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058115142602187/5000000000000000 : ℝ) by norm_num, show 1+2*(2389553409580847143/100000000000000000000 : ℝ)=(52389553409580847143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58115142602187/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58115142602187/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58115142602187/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58115142602187/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58115142602187/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58115142602187/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-472004633/2500000000 : ℝ)*X 0 0+(6051560837/10000000000 : ℝ)*X 0 1+(956397621/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516117681/10000000000 : ℝ)*X 1 0+(-261626353/1000000000 : ℝ)*X 1 1+(597748511/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1379029423/2500000000 : ℝ)*X 2 0+(4781988109/10000000000 : ℝ)*X 2 1+(-2616263491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2100011007/5000000000 : ℝ)*X 0 0+(3120529099/10000000000 : ℝ)*X 0 1+(5652257537/10000000000 : ℝ)*X 0 2+(2100011007/5000000000 : ℝ)*X 1 0+(3120529099/10000000000 : ℝ)*X 1 1+(5652257537/10000000000 : ℝ)*X 1 2+(2100011007/5000000000 : ℝ)*X 2 0+(3120529099/10000000000 : ℝ)*X 2 1+(5652257537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-94656447/500000000 : ℝ)*X 0 0+(4814733449/10000000000 : ℝ)*X 0 1+(1504415821/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171087877/10000000000 : ℝ)*X 1 0+(-138058853/1000000000 : ℝ)*X 1 1+(6017663107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((258554393/500000000 : ℝ)*X 2 0+(6017663163/10000000000 : ℝ)*X 2 1+(-1380588463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2105106547/5000000000 : ℝ)*X 0 0+(34918487/62500000 : ℝ)*X 0 1+(3188126307/10000000000 : ℝ)*X 0 2+(2105106547/5000000000 : ℝ)*X 1 0+(34918487/62500000 : ℝ)*X 1 1+(3188126307/10000000000 : ℝ)*X 1 2+(2105106547/5000000000 : ℝ)*X 2 0+(34918487/62500000 : ℝ)*X 2 1+(3188126307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80641432760478280348239/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4905403/12500000000000 : ℝ)*(base1) + (198188847/25000000000000 : ℝ)*(base19) + (184735349/25000000000000 : ℝ)*(base23) + (5538473/10000000000000 : ℝ)*(base24) + (43672033/25000000000000 : ℝ)*(upper3) + (147832543378201/25000000000000 : ℝ)*(major0) + (147832543378201/25000000000000 : ℝ)*(major1) + (147832543378201/25000000000000 : ℝ)*(major2) + (393834604052497/50000000000000 : ℝ)*(sp0) + (787670147344277/100000000000000 : ℝ)*(sp1) + (39383507288677/5000000000000 : ℝ)*(sp2) + (394987886986917/100000000000000 : ℝ)*(sp3) + (354247579/20000000000000 : ℝ)*(sp4) + (1373173887/100000000000000 : ℝ)*(sp7) + (98747324851007/25000000000000 : ℝ)*(f.failure) + (157534188019933/20000000000000 : ℝ)*(f.sum) + (3048024674413/50000000000000000000000000000 : ℝ)*base66 + (415618565125587/100000000000000000000000000000 : ℝ)*base67 + (353235601925587/100000000000000000000000000000 : ℝ)*base69 + (499605945425587/100000000000000000000000000000 : ℝ)*base71 + (12046919924413/50000000000000000000000000000 : ℝ)*base74 + (495342719325587/100000000000000000000000000000 : ℝ)*base75 + (353045141125587/100000000000000000000000000000 : ℝ)*base77 + (313671962425587/100000000000000000000000000000 : ℝ)*base79 + (226220800825587/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3697721/2500000000000000000000 : ℝ)*base90 + (3697721/2500000000000000000000 : ℝ)*base92 + (3697721/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (419467319762600133073113/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11374843/20000000000000 : ℝ)*(base1) + (1038908307/100000000000000 : ℝ)*(base19) + (207160223/20000000000000 : ℝ)*(base23) + (108450483/100000000000000 : ℝ)*(upper3) + (15628179/12500000000000 : ℝ)*(upper5) + (312043372559789/50000000000000 : ℝ)*(major0) + (312043372559789/50000000000000 : ℝ)*(major1) + (312043372559789/50000000000000 : ℝ)*(major2) + (1037241741/50000000000000 : ℝ)*(sp1) + (2068873903/100000000000000 : ℝ)*(sp2) + (207825946190553/25000000000000 : ℝ)*(sp4) + (51956288406013/6250000000000 : ℝ)*(sp5) + (831300623212979/100000000000000 : ℝ)*(sp6) + (833739131309/200000000000 : ℝ)*(sp7) + (104217405632179/25000000000000 : ℝ)*(f.failure) + (831303727887997/100000000000000 : ℝ)*(f.sum) + (101175927658543/100000000000000000000000000000 : ℝ)*base65 + (426362862058543/200000000000000000000000000000 : ℝ)*base67 + (285574441941457/200000000000000000000000000000 : ℝ)*base70 + (656828968058543/200000000000000000000000000000 : ℝ)*base71 + (31483269658543/100000000000000000000000000000 : ℝ)*base73 + (89078265258543/200000000000000000000000000000 : ℝ)*base75 + (36266736458543/200000000000000000000000000000 : ℝ)*base77 + (232246298858543/200000000000000000000000000000 : ℝ)*base79 + (138592785341457/100000000000000000000000000000 : ℝ)*base82 + (23617563/2500000000000000000000 : ℝ)*base89 + (23617563/2500000000000000000000 : ℝ)*base91 + (23617563/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1154_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (463/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1154_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1154_s1_0 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045907989/5000000000 : ℝ)*x 0 + (356144229/625000000 : ℝ)*x 1 + (1251193723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045907989/5000000000 : ℝ)^8347 ≤ (628889895361/5000000000000 : ℝ)^6299 := by
    have hnat : (1045907989 : ℕ)^8347*5000000000000^6299 ≤ 628889895361^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045907989 5000000000 628889895361 5000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (356144229/625000000 : ℝ)^8347 ≤ (5932548971403/12500000000000 : ℝ)^6299 := by
    have hnat : (356144229 : ℕ)^8347*12500000000000^6299 ≤ 5932548971403^6299*625000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356144229 625000000 5932548971403 12500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251193723/2500000000 : ℝ)^8347 ≤ (39961810303893/100000000000000 : ℝ)^6299 := by
    have hnat : (1251193723 : ℕ)^8347*100000000000000^6299 ≤ 39961810303893^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251193723 2500000000 39961810303893 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045907989/5000000000 : ℝ), (356144229/625000000 : ℝ), (1251193723/2500000000 : ℝ)] ![(628889895361/5000000000000 : ℝ), (5932548971403/12500000000000 : ℝ), (39961810303893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045907989/5000000000 : ℝ)|^8347 ≤ (628889895361/5000000000000 : ℝ)^6299
        have hw : |(-1045907989/5000000000 : ℝ)|=(1045907989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(356144229/625000000 : ℝ)|^8347 ≤ (5932548971403/12500000000000 : ℝ)^6299
        have hw : |(356144229/625000000 : ℝ)|=(356144229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1251193723/2500000000 : ℝ)|^8347 ≤ (39961810303893/100000000000000 : ℝ)^6299
        have hw : |(1251193723/2500000000 : ℝ)|=(1251193723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s1_1 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5418462753/10000000000 : ℝ)*x 0 + (-1232928011/5000000000 : ℝ)*x 1 + (2502387003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418462753/10000000000 : ℝ)^8347 ≤ (44396728314947/100000000000000 : ℝ)^6299 := by
    have hnat : (5418462753 : ℕ)^8347*100000000000000^6299 ≤ 44396728314947^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418462753 10000000000 44396728314947 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232928011/5000000000 : ℝ)^8347 ≤ (15641470741571/100000000000000 : ℝ)^6299 := by
    have hnat : (1232928011 : ℕ)^8347*100000000000000^6299 ≤ 15641470741571^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232928011 5000000000 15641470741571 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2502387003/5000000000 : ℝ)^8347 ≤ (7992360185857/20000000000000 : ℝ)^6299 := by
    have hnat : (2502387003 : ℕ)^8347*20000000000000^6299 ≤ 7992360185857^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502387003 5000000000 7992360185857 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418462753/10000000000 : ℝ), (-1232928011/5000000000 : ℝ), (2502387003/5000000000 : ℝ)] ![(44396728314947/100000000000000 : ℝ), (15641470741571/100000000000000 : ℝ), (7992360185857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418462753/10000000000 : ℝ)|^8347 ≤ (44396728314947/100000000000000 : ℝ)^6299
        have hw : |(5418462753/10000000000 : ℝ)|=(5418462753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1232928011/5000000000 : ℝ)|^8347 ≤ (15641470741571/100000000000000 : ℝ)^6299
        have hw : |(-1232928011/5000000000 : ℝ)|=(1232928011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2502387003/5000000000 : ℝ)|^8347 ≤ (7992360185857/20000000000000 : ℝ)^6299
        have hw : |(2502387003/5000000000 : ℝ)|=(2502387003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s1_2 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2709232413/5000000000 : ℝ)*x 0 + (1251193037/2500000000 : ℝ)*x 1 + (-1232927841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709232413/5000000000 : ℝ)^8347 ≤ (8879350164549/20000000000000 : ℝ)^6299 := by
    have hnat : (2709232413 : ℕ)^8347*20000000000000^6299 ≤ 8879350164549^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709232413 5000000000 8879350164549 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251193037/2500000000 : ℝ)^8347 ≤ (999044531753/2500000000000 : ℝ)^6299 := by
    have hnat : (1251193037 : ℕ)^8347*2500000000000^6299 ≤ 999044531753^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251193037 2500000000 999044531753 2500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1232927841/5000000000 : ℝ)^8347 ≤ (3910366970917/25000000000000 : ℝ)^6299 := by
    have hnat : (1232927841 : ℕ)^8347*25000000000000^6299 ≤ 3910366970917^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232927841 5000000000 3910366970917 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709232413/5000000000 : ℝ), (1251193037/2500000000 : ℝ), (-1232927841/5000000000 : ℝ)] ![(8879350164549/20000000000000 : ℝ), (999044531753/2500000000000 : ℝ), (3910366970917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709232413/5000000000 : ℝ)|^8347 ≤ (8879350164549/20000000000000 : ℝ)^6299
        have hw : |(2709232413/5000000000 : ℝ)|=(2709232413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251193037/2500000000 : ℝ)|^8347 ≤ (999044531753/2500000000000 : ℝ)^6299
        have hw : |(1251193037/2500000000 : ℝ)|=(1251193037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1232927841/5000000000 : ℝ)|^8347 ≤ (3910366970917/25000000000000 : ℝ)^6299
        have hw : |(-1232927841/5000000000 : ℝ)|=(1232927841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s1_3 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1726569/4000000 : ℝ)*x 0 + (459912203/1250000000 : ℝ)*x 1 + (506230781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1726569/4000000 : ℝ)^8347 ≤ (8211669285551/25000000000000 : ℝ)^6299 := by
    have hnat : (1726569 : ℕ)^8347*25000000000000^6299 ≤ 8211669285551^6299*4000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726569 4000000 8211669285551 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459912203/1250000000 : ℝ)^8347 ≤ (13290816140033/50000000000000 : ℝ)^6299 := by
    have hnat : (459912203 : ℕ)^8347*50000000000000^6299 ≤ 13290816140033^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459912203 1250000000 13290816140033 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506230781/1000000000 : ℝ)^8347 ≤ (40571690560817/100000000000000 : ℝ)^6299 := by
    have hnat : (506230781 : ℕ)^8347*100000000000000^6299 ≤ 40571690560817^6299*1000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506230781 1000000000 40571690560817 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1726569/4000000 : ℝ), (459912203/1250000000 : ℝ), (506230781/1000000000 : ℝ)] ![(8211669285551/25000000000000 : ℝ), (13290816140033/50000000000000 : ℝ), (40571690560817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1726569/4000000 : ℝ)|^8347 ≤ (8211669285551/25000000000000 : ℝ)^6299
        have hw : |(1726569/4000000 : ℝ)|=(1726569/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(459912203/1250000000 : ℝ)|^8347 ≤ (13290816140033/50000000000000 : ℝ)^6299
        have hw : |(459912203/1250000000 : ℝ)|=(459912203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(506230781/1000000000 : ℝ)|^8347 ≤ (40571690560817/100000000000000 : ℝ)^6299
        have hw : |(506230781/1000000000 : ℝ)|=(506230781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s1_4 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046305029/5000000000 : ℝ)*x 0 + (626775139/1250000000 : ℝ)*x 1 + (5688692193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046305029/5000000000 : ℝ)^8347 ≤ (12584125390373/100000000000000 : ℝ)^6299 := by
    have hnat : (1046305029 : ℕ)^8347*100000000000000^6299 ≤ 12584125390373^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046305029 5000000000 12584125390373 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626775139/1250000000 : ℝ)^8347 ≤ (40061577985317/100000000000000 : ℝ)^6299 := by
    have hnat : (626775139 : ℕ)^8347*100000000000000^6299 ≤ 40061577985317^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626775139 1250000000 40061577985317 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5688692193/10000000000 : ℝ)^8347 ≤ (23677148302653/50000000000000 : ℝ)^6299 := by
    have hnat : (5688692193 : ℕ)^8347*50000000000000^6299 ≤ 23677148302653^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688692193 10000000000 23677148302653 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046305029/5000000000 : ℝ), (626775139/1250000000 : ℝ), (5688692193/10000000000 : ℝ)] ![(12584125390373/100000000000000 : ℝ), (40061577985317/100000000000000 : ℝ), (23677148302653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046305029/5000000000 : ℝ)|^8347 ≤ (12584125390373/100000000000000 : ℝ)^6299
        have hw : |(-1046305029/5000000000 : ℝ)|=(1046305029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626775139/1250000000 : ℝ)|^8347 ≤ (40061577985317/100000000000000 : ℝ)^6299
        have hw : |(626775139/1250000000 : ℝ)|=(626775139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5688692193/10000000000 : ℝ)|^8347 ≤ (23677148302653/50000000000000 : ℝ)^6299
        have hw : |(5688692193/10000000000 : ℝ)|=(5688692193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s1_5 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (52405467/100000000 : ℝ)*x 0 + (-44548347/250000000 : ℝ)*x 1 + (711086971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52405467/100000000 : ℝ)^8347 ≤ (21237688138457/50000000000000 : ℝ)^6299 := by
    have hnat : (52405467 : ℕ)^8347*50000000000000^6299 ≤ 21237688138457^6299*100000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52405467 100000000 21237688138457 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44548347/250000000 : ℝ)^8347 ≤ (2034057533963/20000000000000 : ℝ)^6299 := by
    have hnat : (44548347 : ℕ)^8347*20000000000000^6299 ≤ 2034057533963^6299*250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44548347 250000000 2034057533963 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711086971/1250000000 : ℝ)^8347 ≤ (23677168020153/50000000000000 : ℝ)^6299 := by
    have hnat : (711086971 : ℕ)^8347*50000000000000^6299 ≤ 23677168020153^6299*1250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711086971 1250000000 23677168020153 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52405467/100000000 : ℝ), (-44548347/250000000 : ℝ), (711086971/1250000000 : ℝ)] ![(21237688138457/50000000000000 : ℝ), (2034057533963/20000000000000 : ℝ), (23677168020153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52405467/100000000 : ℝ)|^8347 ≤ (21237688138457/50000000000000 : ℝ)^6299
        have hw : |(52405467/100000000 : ℝ)|=(52405467/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44548347/250000000 : ℝ)|^8347 ≤ (2034057533963/20000000000000 : ℝ)^6299
        have hw : |(-44548347/250000000 : ℝ)|=(44548347/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(711086971/1250000000 : ℝ)|^8347 ≤ (23677168020153/50000000000000 : ℝ)^6299
        have hw : |(711086971/1250000000 : ℝ)|=(711086971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s1_6 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5240545519/10000000000 : ℝ)*x 0 + (5688697433/10000000000 : ℝ)*x 1 + (-1781933129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240545519/10000000000 : ℝ)^8347 ≤ (10618840898133/25000000000000 : ℝ)^6299 := by
    have hnat : (5240545519 : ℕ)^8347*25000000000000^6299 ≤ 10618840898133^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240545519 10000000000 10618840898133 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5688697433/10000000000 : ℝ)^8347 ≤ (2367717720327/5000000000000 : ℝ)^6299 := by
    have hnat : (5688697433 : ℕ)^8347*5000000000000^6299 ≤ 2367717720327^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688697433 10000000000 2367717720327 5000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1781933129/10000000000 : ℝ)^8347 ≤ (10170281989919/100000000000000 : ℝ)^6299 := by
    have hnat : (1781933129 : ℕ)^8347*100000000000000^6299 ≤ 10170281989919^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781933129 10000000000 10170281989919 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240545519/10000000000 : ℝ), (5688697433/10000000000 : ℝ), (-1781933129/10000000000 : ℝ)] ![(10618840898133/25000000000000 : ℝ), (2367717720327/5000000000000 : ℝ), (10170281989919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240545519/10000000000 : ℝ)|^8347 ≤ (10618840898133/25000000000000 : ℝ)^6299
        have hw : |(5240545519/10000000000 : ℝ)|=(5240545519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5688697433/10000000000 : ℝ)|^8347 ≤ (2367717720327/5000000000000 : ℝ)^6299
        have hw : |(5688697433/10000000000 : ℝ)|=(5688697433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1781933129/10000000000 : ℝ)|^8347 ≤ (10170281989919/100000000000000 : ℝ)^6299
        have hw : |(-1781933129/10000000000 : ℝ)|=(1781933129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s1_7 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2158997357/5000000000 : ℝ)*x 0 + (1008702329/2000000000 : ℝ)*x 1 + (92461593/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158997357/5000000000 : ℝ)^8347 ≤ (8215633012049/25000000000000 : ℝ)^6299 := by
    have hnat : (2158997357 : ℕ)^8347*25000000000000^6299 ≤ 8215633012049^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158997357 5000000000 8215633012049 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008702329/2000000000 : ℝ)^8347 ≤ (40372191814343/100000000000000 : ℝ)^6299 := by
    have hnat : (1008702329 : ℕ)^8347*100000000000000^6299 ≤ 40372191814343^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008702329 2000000000 40372191814343 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92461593/250000000 : ℝ)^8347 ≤ (26765276125921/100000000000000 : ℝ)^6299 := by
    have hnat : (92461593 : ℕ)^8347*100000000000000^6299 ≤ 26765276125921^6299*250000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92461593 250000000 26765276125921 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158997357/5000000000 : ℝ), (1008702329/2000000000 : ℝ), (92461593/250000000 : ℝ)] ![(8215633012049/25000000000000 : ℝ), (40372191814343/100000000000000 : ℝ), (26765276125921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158997357/5000000000 : ℝ)|^8347 ≤ (8215633012049/25000000000000 : ℝ)^6299
        have hw : |(2158997357/5000000000 : ℝ)|=(2158997357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008702329/2000000000 : ℝ)|^8347 ≤ (40372191814343/100000000000000 : ℝ)^6299
        have hw : |(1008702329/2000000000 : ℝ)|=(1008702329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(92461593/250000000 : ℝ)|^8347 ≤ (26765276125921/100000000000000 : ℝ)^6299
        have hw : |(92461593/250000000 : ℝ)|=(92461593/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1154_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5717/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20383/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (463/100000 : ℝ) ^ (4173/1024 : ℝ) ≤ (15337571543/50000000000000000000 : ℝ) := by
    have hpowers : (463/100000 : ℝ)^4173 ≤ (15337571543/50000000000000000000 : ℝ)^1024 := by
      have hnat : (463 : ℕ)^4173*50000000000000000000^1024 ≤ 15337571543^1024*100000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        463 100000 15337571543 50000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (463/100000 : ℝ)) (X := (15337571543/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27769/100000 : ℝ) ^ (4173/1024 : ℝ) ≤ (540006889112481691/100000000000000000000 : ℝ) := by
    have hpowers : (27769/100000 : ℝ)^4173 ≤ (540006889112481691/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27769 : ℕ)^4173*100000000000000000000^1024 ≤ 540006889112481691^1024*100000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27769 100000 540006889112481691 100000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27769/100000 : ℝ)) (X := (540006889112481691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000015337571543/25000000000000000000 : ℝ) ≤ (10000000001505457/10000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (25000000015337571543/25000000000000000000 : ℝ)^1024 ≤ (10000000001505457/10000000000000000 : ℝ)^4173 := by
      have hnat : (25000000015337571543 : ℕ)^1024*10000000000000000^4173 ≤ 10000000001505457^4173*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000015337571543 25000000000000000000 10000000001505457 10000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001505457/10000000000000000 : ℝ)) (X := (25000000015337571543/25000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100540006919787624777/100000000000000000000 : ℝ) ≤ (5006612077294919/5000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (100540006919787624777/100000000000000000000 : ℝ)^1024 ≤ (5006612077294919/5000000000000000 : ℝ)^4173 := by
      have hnat : (100540006919787624777 : ℕ)^1024*5000000000000000^4173 ≤ 5006612077294919^4173*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100540006919787624777 100000000000000000000 5006612077294919 5000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006612077294919/5000000000000000 : ℝ)) (X := (100540006919787624777/100000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50540006889112481691/50000000000000000000 : ℝ) ≤ (10026448307674219/10000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (50540006889112481691/50000000000000000000 : ℝ)^1024 ≤ (10026448307674219/10000000000000000 : ℝ)^4173 := by
      have hnat : (50540006889112481691 : ℕ)^1024*10000000000000000^4173 ≤ 10026448307674219^4173*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50540006889112481691 50000000000000000000 10026448307674219 10000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026448307674219/10000000000000000 : ℝ)) (X := (50540006889112481691/50000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15337571543/50000000000000000000 : ℝ) ≤ ((7584659846537552001/7585000000000000000 : ℝ)+2*(1469350342709/303400000000000 : ℝ)*(463/100000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (7584659846537552001/7585000000000000000 : ℝ)+2*(1469350342709/303400000000000 : ℝ)*(463/100000 : ℝ)=(10000000001505457/10000000000000000 : ℝ) by norm_num, show 1+2*(15337571543/50000000000000000000 : ℝ)=(25000000015337571543/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(540006889112481691/100000000000000000000 : ℝ)+(15337571543/50000000000000000000 : ℝ) ≤ ((7584659846537552001/7585000000000000000 : ℝ)+(1469350342709/303400000000000 : ℝ)*((27769/100000 : ℝ)+(463/100000 : ℝ)))^(4173/1024 : ℝ) := by
    rw [show (7584659846537552001/7585000000000000000 : ℝ)+(1469350342709/303400000000000 : ℝ)*((27769/100000 : ℝ)+(463/100000 : ℝ))=(5006612077294919/5000000000000000 : ℝ) by norm_num, show 1+(540006889112481691/100000000000000000000 : ℝ)+(15337571543/50000000000000000000 : ℝ)=(100540006919787624777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(540006889112481691/100000000000000000000 : ℝ) ≤ ((7584659846537552001/7585000000000000000 : ℝ)+2*(1469350342709/303400000000000 : ℝ)*(27769/100000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (7584659846537552001/7585000000000000000 : ℝ)+2*(1469350342709/303400000000000 : ℝ)*(27769/100000 : ℝ)=(10026448307674219/10000000000000000 : ℝ) by norm_num, show 1+2*(540006889112481691/100000000000000000000 : ℝ)=(50540006889112481691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7584659846537552001/7585000000000000000 : ℝ)*(X 1 0+X 2 0)+(1469350342709/303400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (463/100000 : ℝ)) (hi := (27769/100000 : ℝ)) (c := (7584659846537552001/7585000000000000000 : ℝ)) (alpha := (1469350342709/303400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7584659846537552001/7585000000000000000 : ℝ)*(X 0 1+X 2 1)+(1469350342709/303400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (463/100000 : ℝ)) (hi := (27769/100000 : ℝ)) (c := (7584659846537552001/7585000000000000000 : ℝ)) (alpha := (1469350342709/303400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7584659846537552001/7585000000000000000 : ℝ)*(X 0 2+X 1 2)+(1469350342709/303400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (463/100000 : ℝ)) (hi := (27769/100000 : ℝ)) (c := (7584659846537552001/7585000000000000000 : ℝ)) (alpha := (1469350342709/303400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1045907989/5000000000 : ℝ)*X 0 0+(356144229/625000000 : ℝ)*X 0 1+(1251193723/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5418462753/10000000000 : ℝ)*X 1 0+(-1232928011/5000000000 : ℝ)*X 1 1+(2502387003/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2709232413/5000000000 : ℝ)*X 2 0+(1251193037/2500000000 : ℝ)*X 2 1+(-1232927841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1726569/4000000 : ℝ)*X 0 0+(459912203/1250000000 : ℝ)*X 0 1+(506230781/1000000000 : ℝ)*X 0 2+(1726569/4000000 : ℝ)*X 1 0+(459912203/1250000000 : ℝ)*X 1 1+(506230781/1000000000 : ℝ)*X 1 2+(1726569/4000000 : ℝ)*X 2 0+(459912203/1250000000 : ℝ)*X 2 1+(506230781/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1046305029/5000000000 : ℝ)*X 0 0+(626775139/1250000000 : ℝ)*X 0 1+(5688692193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((52405467/100000000 : ℝ)*X 1 0+(-44548347/250000000 : ℝ)*X 1 1+(711086971/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5240545519/10000000000 : ℝ)*X 2 0+(5688697433/10000000000 : ℝ)*X 2 1+(-1781933129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158997357/5000000000 : ℝ)*X 0 0+(1008702329/2000000000 : ℝ)*X 0 1+(92461593/250000000 : ℝ)*X 0 2+(2158997357/5000000000 : ℝ)*X 1 0+(1008702329/2000000000 : ℝ)*X 1 1+(92461593/250000000 : ℝ)*X 1 2+(2158997357/5000000000 : ℝ)*X 2 0+(1008702329/2000000000 : ℝ)*X 2 1+(92461593/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1217377624047688930251/1517000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6093027/50000000000000 : ℝ)*(base1) + (537532443/100000000000000 : ℝ)*(base19) + (258008453/50000000000000 : ℝ)*(base23) + (339706931/100000000000000 : ℝ)*(lower2) + (11906741/20000000000000 : ℝ)*(lower4) + (108247690944701/10000000000000 : ℝ)*(major0) + (108247690944701/10000000000000 : ℝ)*(major1) + (108247690944701/10000000000000 : ℝ)*(major2) + (360473127610887/25000000000000 : ℝ)*(sp0) + (288378785932117/20000000000000 : ℝ)*(sp1) + (360473060781589/25000000000000 : ℝ)*(sp2) + (723059312765261/100000000000000 : ℝ)*(sp3) + (1968935533/100000000000000 : ℝ)*(sp4) + (854024883/50000000000000 : ℝ)*(sp6) + (144611864990263/20000000000000 : ℝ)*(f.failure) + (1441894467193027/100000000000000 : ℝ)*(f.sum) + (743402289181/303400000000000000000000000 : ℝ)*base66 + (195305351810921701/75850000000000000000000000000000 : ℝ)*base67 + (293555778622371701/75850000000000000000000000000000 : ℝ)*base69 + (134525230951128299/75850000000000000000000000000000 : ℝ)*base72 + (3241808345111/1517000000000000000000000000 : ℝ)*base73 + (184266061653878299/75850000000000000000000000000000 : ℝ)*base76 + (585465776615378299/75850000000000000000000000000000 : ℝ)*base78 + (73845320982621701/75850000000000000000000000000000 : ℝ)*base79 + (4264890120341/1517000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (793089/2000000000000000000000 : ℝ)*base90 + (793089/2000000000000000000000 : ℝ)*base92 + (793089/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (363047342336207694654446403/379250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2141158699/100000000000000 : ℝ)*(base19) + (705397239/25000000000000 : ℝ)*(base23) + (105252829/25000000000000 : ℝ)*(upper2) + (606289447/100000000000000 : ℝ)*(upper3) + (336480443/100000000000000 : ℝ)*(upper5) + (1113031063932267/100000000000000 : ℝ)*(major0) + (1113031063932267/100000000000000 : ℝ)*(major1) + (1113031063932267/100000000000000 : ℝ)*(major2) + (12382358119/100000000000000 : ℝ)*(sp1) + (4650525871/25000000000000 : ℝ)*(sp2) + (741296795397681/50000000000000 : ℝ)*(sp4) + (92661191704909/6250000000000 : ℝ)*(sp5) + (741286083551461/50000000000000 : ℝ)*(sp6) + (74346850515993/10000000000000 : ℝ)*(sp7) + (74346850515993/10000000000000 : ℝ)*(f.failure) + (741296795397681/50000000000000 : ℝ)*(f.sum) + (57932294102777/15170000000000000000000000000 : ℝ)*base66 + (1191928865012108733/758500000000000000000000000000000 : ℝ)*base68 + (5995904598124108733/758500000000000000000000000000000 : ℝ)*base70 + (5318721836542608733/758500000000000000000000000000000 : ℝ)*base72 + (51429104545737/15170000000000000000000000000 : ℝ)*base74 + (2214211433064108733/758500000000000000000000000000000 : ℝ)*base76 + (6013745925900108733/758500000000000000000000000000000 : ℝ)*base78 + (3664881823181108733/758500000000000000000000000000000 : ℝ)*base80 + (78278018216277/15170000000000000000000000000 : ℝ)*base82 + (6896721/1000000000000000000000 : ℝ)*base89 + (6896721/1000000000000000000000 : ℝ)*base91 + (6896721/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1154_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5717/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20383/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1154_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1154_s2_0 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144404711/10000000000 : ℝ)*x 0 + (5508535889/10000000000 : ℝ)*x 1 + (5161094669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144404711/10000000000 : ℝ)^8347 ≤ (12998518792233/100000000000000 : ℝ)^6299 := by
    have hnat : (2144404711 : ℕ)^8347*100000000000000^6299 ≤ 12998518792233^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144404711 10000000000 12998518792233 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508535889/10000000000 : ℝ)^8347 ≤ (11344334775039/25000000000000 : ℝ)^6299 := by
    have hnat : (5508535889 : ℕ)^8347*25000000000000^6299 ≤ 11344334775039^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508535889 10000000000 11344334775039 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5161094669/10000000000 : ℝ)^8347 ≤ (20812071046237/50000000000000 : ℝ)^6299 := by
    have hnat : (5161094669 : ℕ)^8347*50000000000000^6299 ≤ 20812071046237^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161094669 10000000000 20812071046237 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144404711/10000000000 : ℝ), (5508535889/10000000000 : ℝ), (5161094669/10000000000 : ℝ)] ![(12998518792233/100000000000000 : ℝ), (11344334775039/25000000000000 : ℝ), (20812071046237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144404711/10000000000 : ℝ)|^8347 ≤ (12998518792233/100000000000000 : ℝ)^6299
        have hw : |(-2144404711/10000000000 : ℝ)|=(2144404711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508535889/10000000000 : ℝ)|^8347 ≤ (11344334775039/25000000000000 : ℝ)^6299
        have hw : |(5508535889/10000000000 : ℝ)|=(5508535889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5161094669/10000000000 : ℝ)|^8347 ≤ (20812071046237/50000000000000 : ℝ)^6299
        have hw : |(5161094669/10000000000 : ℝ)|=(5161094669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s2_1 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686674769/5000000000 : ℝ)*x 0 + (-2324955167/10000000000 : ℝ)*x 1 + (2580548517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686674769/5000000000 : ℝ)^8347 ≤ (21953785732659/50000000000000 : ℝ)^6299 := by
    have hnat : (2686674769 : ℕ)^8347*50000000000000^6299 ≤ 21953785732659^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686674769 5000000000 21953785732659 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2324955167/10000000000 : ℝ)^8347 ≤ (14468261156497/100000000000000 : ℝ)^6299 := by
    have hnat : (2324955167 : ℕ)^8347*100000000000000^6299 ≤ 14468261156497^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2324955167 10000000000 14468261156497 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2580548517/5000000000 : ℝ)^8347 ≤ (5203020920951/12500000000000 : ℝ)^6299 := by
    have hnat : (2580548517 : ℕ)^8347*12500000000000^6299 ≤ 5203020920951^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580548517 5000000000 5203020920951 12500000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686674769/5000000000 : ℝ), (-2324955167/10000000000 : ℝ), (2580548517/5000000000 : ℝ)] ![(21953785732659/50000000000000 : ℝ), (14468261156497/100000000000000 : ℝ), (5203020920951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686674769/5000000000 : ℝ)|^8347 ≤ (21953785732659/50000000000000 : ℝ)^6299
        have hw : |(2686674769/5000000000 : ℝ)|=(2686674769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2324955167/10000000000 : ℝ)|^8347 ≤ (14468261156497/100000000000000 : ℝ)^6299
        have hw : |(-2324955167/10000000000 : ℝ)|=(2324955167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2580548517/5000000000 : ℝ)|^8347 ≤ (5203020920951/12500000000000 : ℝ)^6299
        have hw : |(2580548517/5000000000 : ℝ)|=(2580548517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s2_2 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686674857/5000000000 : ℝ)*x 0 + (5161096613/10000000000 : ℝ)*x 1 + (-1162477741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686674857/5000000000 : ℝ)^8347 ≤ (43907573371067/100000000000000 : ℝ)^6299 := by
    have hnat : (2686674857 : ℕ)^8347*100000000000000^6299 ≤ 43907573371067^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686674857 5000000000 43907573371067 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5161096613/10000000000 : ℝ)^8347 ≤ (41624162868313/100000000000000 : ℝ)^6299 := by
    have hnat : (5161096613 : ℕ)^8347*100000000000000^6299 ≤ 41624162868313^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161096613 10000000000 41624162868313 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1162477741/5000000000 : ℝ)^8347 ≤ (1446826375409/10000000000000 : ℝ)^6299 := by
    have hnat : (1162477741 : ℕ)^8347*10000000000000^6299 ≤ 1446826375409^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162477741 5000000000 1446826375409 10000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686674857/5000000000 : ℝ), (5161096613/10000000000 : ℝ), (-1162477741/5000000000 : ℝ)] ![(43907573371067/100000000000000 : ℝ), (41624162868313/100000000000000 : ℝ), (1446826375409/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686674857/5000000000 : ℝ)|^8347 ≤ (43907573371067/100000000000000 : ℝ)^6299
        have hw : |(2686674857/5000000000 : ℝ)|=(2686674857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5161096613/10000000000 : ℝ)|^8347 ≤ (41624162868313/100000000000000 : ℝ)^6299
        have hw : |(5161096613/10000000000 : ℝ)|=(5161096613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1162477741/5000000000 : ℝ)|^8347 ≤ (1446826375409/10000000000000 : ℝ)^6299
        have hw : |(-1162477741/5000000000 : ℝ)|=(1162477741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s2_3 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870506067/2000000000 : ℝ)*x 0 + (251233191/625000000 : ℝ)*x 1 + (2356289413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870506067/2000000000 : ℝ)^8347 ≤ (6642255457387/20000000000000 : ℝ)^6299 := by
    have hnat : (870506067 : ℕ)^8347*20000000000000^6299 ≤ 6642255457387^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870506067 2000000000 6642255457387 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251233191/625000000 : ℝ)^8347 ≤ (5977769672023/20000000000000 : ℝ)^6299 := by
    have hnat : (251233191 : ℕ)^8347*20000000000000^6299 ≤ 5977769672023^6299*625000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251233191 625000000 5977769672023 20000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2356289413/5000000000 : ℝ)^8347 ≤ (36899874341069/100000000000000 : ℝ)^6299 := by
    have hnat : (2356289413 : ℕ)^8347*100000000000000^6299 ≤ 36899874341069^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356289413 5000000000 36899874341069 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870506067/2000000000 : ℝ), (251233191/625000000 : ℝ), (2356289413/5000000000 : ℝ)] ![(6642255457387/20000000000000 : ℝ), (5977769672023/20000000000000 : ℝ), (36899874341069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870506067/2000000000 : ℝ)|^8347 ≤ (6642255457387/20000000000000 : ℝ)^6299
        have hw : |(870506067/2000000000 : ℝ)|=(870506067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251233191/625000000 : ℝ)|^8347 ≤ (5977769672023/20000000000000 : ℝ)^6299
        have hw : |(251233191/625000000 : ℝ)|=(251233191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2356289413/5000000000 : ℝ)|^8347 ≤ (36899874341069/100000000000000 : ℝ)^6299
        have hw : |(2356289413/5000000000 : ℝ)|=(2356289413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s2_4 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2144504107/10000000000 : ℝ)*x 0 + (5163470559/10000000000 : ℝ)*x 1 + (5506136313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144504107/10000000000 : ℝ)^8347 ≤ (6499658593883/50000000000000 : ℝ)^6299 := by
    have hnat : (2144504107 : ℕ)^8347*50000000000000^6299 ≤ 6499658593883^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144504107 10000000000 6499658593883 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5163470559/10000000000 : ℝ)^8347 ≤ (41649535506949/100000000000000 : ℝ)^6299 := by
    have hnat : (5163470559 : ℕ)^8347*100000000000000^6299 ≤ 41649535506949^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163470559 10000000000 41649535506949 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5506136313/10000000000 : ℝ)^8347 ≤ (45351147296997/100000000000000 : ℝ)^6299 := by
    have hnat : (5506136313 : ℕ)^8347*100000000000000^6299 ≤ 45351147296997^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506136313 10000000000 45351147296997 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2144504107/10000000000 : ℝ), (5163470559/10000000000 : ℝ), (5506136313/10000000000 : ℝ)] ![(6499658593883/50000000000000 : ℝ), (41649535506949/100000000000000 : ℝ), (45351147296997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2144504107/10000000000 : ℝ)|^8347 ≤ (6499658593883/50000000000000 : ℝ)^6299
        have hw : |(-2144504107/10000000000 : ℝ)|=(2144504107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5163470559/10000000000 : ℝ)|^8347 ≤ (41649535506949/100000000000000 : ℝ)^6299
        have hw : |(5163470559/10000000000 : ℝ)|=(5163470559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5506136313/10000000000 : ℝ)|^8347 ≤ (45351147296997/100000000000000 : ℝ)^6299
        have hw : |(5506136313/10000000000 : ℝ)|=(5506136313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s2_5 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321281053/2500000000 : ℝ)*x 0 + (-395982701/2000000000 : ℝ)*x 1 + (5506137111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321281053/2500000000 : ℝ)^8347 ≤ (42954816277819/100000000000000 : ℝ)^6299 := by
    have hnat : (1321281053 : ℕ)^8347*100000000000000^6299 ≤ 42954816277819^6299*2500000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321281053 2500000000 42954816277819 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395982701/2000000000 : ℝ)^8347 ≤ (11694027703147/100000000000000 : ℝ)^6299 := by
    have hnat : (395982701 : ℕ)^8347*100000000000000^6299 ≤ 11694027703147^6299*2000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395982701 2000000000 11694027703147 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5506137111/10000000000 : ℝ)^8347 ≤ (45351156006693/100000000000000 : ℝ)^6299 := by
    have hnat : (5506137111 : ℕ)^8347*100000000000000^6299 ≤ 45351156006693^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506137111 10000000000 45351156006693 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321281053/2500000000 : ℝ), (-395982701/2000000000 : ℝ), (5506137111/10000000000 : ℝ)] ![(42954816277819/100000000000000 : ℝ), (11694027703147/100000000000000 : ℝ), (45351156006693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321281053/2500000000 : ℝ)|^8347 ≤ (42954816277819/100000000000000 : ℝ)^6299
        have hw : |(1321281053/2500000000 : ℝ)|=(1321281053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395982701/2000000000 : ℝ)|^8347 ≤ (11694027703147/100000000000000 : ℝ)^6299
        have hw : |(-395982701/2000000000 : ℝ)|=(395982701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5506137111/10000000000 : ℝ)|^8347 ≤ (45351156006693/100000000000000 : ℝ)^6299
        have hw : |(5506137111/10000000000 : ℝ)|=(5506137111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s2_6 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285122489/10000000000 : ℝ)*x 0 + (2753068407/5000000000 : ℝ)*x 1 + (-197991629/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285122489/10000000000 : ℝ)^8347 ≤ (268467485757/625000000000 : ℝ)^6299 := by
    have hnat : (5285122489 : ℕ)^8347*625000000000^6299 ≤ 268467485757^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285122489 10000000000 268467485757 625000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753068407/5000000000 : ℝ)^8347 ≤ (22675576382557/50000000000000 : ℝ)^6299 := by
    have hnat : (2753068407 : ℕ)^8347*50000000000000^6299 ≤ 22675576382557^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753068407 5000000000 22675576382557 50000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197991629/1000000000 : ℝ)^8347 ≤ (2923512375103/25000000000000 : ℝ)^6299 := by
    have hnat : (197991629 : ℕ)^8347*25000000000000^6299 ≤ 2923512375103^6299*1000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197991629 1000000000 2923512375103 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285122489/10000000000 : ℝ), (2753068407/5000000000 : ℝ), (-197991629/1000000000 : ℝ)] ![(268467485757/625000000000 : ℝ), (22675576382557/50000000000000 : ℝ), (2923512375103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285122489/10000000000 : ℝ)|^8347 ≤ (268467485757/625000000000 : ℝ)^6299
        have hw : |(5285122489/10000000000 : ℝ)|=(5285122489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753068407/5000000000 : ℝ)|^8347 ≤ (22675576382557/50000000000000 : ℝ)^6299
        have hw : |(2753068407/5000000000 : ℝ)|=(2753068407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197991629/1000000000 : ℝ)|^8347 ≤ (2923512375103/25000000000000 : ℝ)^6299
        have hw : |(-197991629/1000000000 : ℝ)|=(197991629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1154_s2_7 (p : ℝ) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352727231/10000000000 : ℝ)*x 0 + (4707842937/10000000000 : ℝ)*x 1 + (2012257223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352727231/10000000000 : ℝ)^8347 ≤ (8303317038961/25000000000000 : ℝ)^6299 := by
    have hnat : (4352727231 : ℕ)^8347*25000000000000^6299 ≤ 8303317038961^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352727231 10000000000 8303317038961 25000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4707842937/10000000000 : ℝ)^8347 ≤ (1474029733627/4000000000000 : ℝ)^6299 := by
    have hnat : (4707842937 : ℕ)^8347*4000000000000^6299 ≤ 1474029733627^6299*10000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4707842937 10000000000 1474029733627 4000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012257223/5000000000 : ℝ)^8347 ≤ (29935988488859/100000000000000 : ℝ)^6299 := by
    have hnat : (2012257223 : ℕ)^8347*100000000000000^6299 ≤ 29935988488859^6299*5000000000^8347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012257223 5000000000 29935988488859 100000000000000 8347 6299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8347/2048 : ℝ)) 8347 6299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352727231/10000000000 : ℝ), (4707842937/10000000000 : ℝ), (2012257223/5000000000 : ℝ)] ![(8303317038961/25000000000000 : ℝ), (1474029733627/4000000000000 : ℝ), (29935988488859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352727231/10000000000 : ℝ)|^8347 ≤ (8303317038961/25000000000000 : ℝ)^6299
        have hw : |(4352727231/10000000000 : ℝ)|=(4352727231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4707842937/10000000000 : ℝ)|^8347 ≤ (1474029733627/4000000000000 : ℝ)^6299
        have hw : |(4707842937/10000000000 : ℝ)|=(4707842937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012257223/5000000000 : ℝ)|^8347 ≤ (29935988488859/100000000000000 : ℝ)^6299
        have hw : |(2012257223/5000000000 : ℝ)|=(2012257223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1154_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2281/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16467/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5717/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5717/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5717/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5717/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5717/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5717/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5717/100000 : ℝ) ^ (4173/1024 : ℝ) ≤ (53839083713719/6250000000000000000 : ℝ) := by
    have hpowers : (5717/100000 : ℝ)^4173 ≤ (53839083713719/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5717 : ℕ)^4173*6250000000000000000^1024 ≤ 53839083713719^1024*100000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5717 100000 53839083713719 6250000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5717/100000 : ℝ)) (X := (53839083713719/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20383/100000 : ℝ) ^ (4173/1024 : ℝ) ≤ (76577753474701877/50000000000000000000 : ℝ) := by
    have hpowers : (20383/100000 : ℝ)^4173 ≤ (76577753474701877/50000000000000000000 : ℝ)^1024 := by
      have hnat : (20383 : ℕ)^4173*50000000000000000000^1024 ≤ 76577753474701877^1024*100000^4173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20383 100000 76577753474701877 50000000000000000000 4173 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20383/100000 : ℝ)) (X := (76577753474701877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125053839083713719/3125000000000000000 : ℝ) ≤ (2500010569060791/2500000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (3125053839083713719/3125000000000000000 : ℝ)^1024 ≤ (2500010569060791/2500000000000000 : ℝ)^4173 := by
      have hnat : (3125053839083713719 : ℕ)^1024*2500000000000000^4173 ≤ 2500010569060791^4173*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125053839083713719 3125000000000000000 2500010569060791 2500000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500010569060791/2500000000000000 : ℝ)) (X := (3125053839083713719/3125000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50077008466144411629/50000000000000000000 : ℝ) ≤ (5001888590599181/5000000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (50077008466144411629/50000000000000000000 : ℝ)^1024 ≤ (5001888590599181/5000000000000000 : ℝ)^4173 := by
      have hnat : (50077008466144411629 : ℕ)^1024*5000000000000000^4173 ≤ 5001888590599181^4173*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50077008466144411629 50000000000000000000 5001888590599181 5000000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001888590599181/5000000000000000 : ℝ)) (X := (50077008466144411629/50000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25076577753474701877/25000000000000000000 : ℝ) ≤ (250187802153839/250000000000000 : ℝ) ^ (4173/1024 : ℝ) := by
    have hpowers : (25076577753474701877/25000000000000000000 : ℝ)^1024 ≤ (250187802153839/250000000000000 : ℝ)^4173 := by
      have hnat : (25076577753474701877 : ℕ)^1024*250000000000000^4173 ≤ 250187802153839^4173*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25076577753474701877 25000000000000000000 250187802153839 250000000000000 1024 4173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250187802153839/250000000000000 : ℝ)) (X := (25076577753474701877/25000000000000000000 : ℝ)) (by norm_num) 4173 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53839083713719/6250000000000000000 : ℝ) ≤ ((36654478780031127323/36665000000000000000 : ℝ)+2*(1867452477599/733300000000000 : ℝ)*(5717/100000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (36654478780031127323/36665000000000000000 : ℝ)+2*(1867452477599/733300000000000 : ℝ)*(5717/100000 : ℝ)=(2500010569060791/2500000000000000 : ℝ) by norm_num, show 1+2*(53839083713719/6250000000000000000 : ℝ)=(3125053839083713719/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76577753474701877/50000000000000000000 : ℝ)+(53839083713719/6250000000000000000 : ℝ) ≤ ((36654478780031127323/36665000000000000000 : ℝ)+(1867452477599/733300000000000 : ℝ)*((20383/100000 : ℝ)+(5717/100000 : ℝ)))^(4173/1024 : ℝ) := by
    rw [show (36654478780031127323/36665000000000000000 : ℝ)+(1867452477599/733300000000000 : ℝ)*((20383/100000 : ℝ)+(5717/100000 : ℝ))=(5001888590599181/5000000000000000 : ℝ) by norm_num, show 1+(76577753474701877/50000000000000000000 : ℝ)+(53839083713719/6250000000000000000 : ℝ)=(50077008466144411629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76577753474701877/50000000000000000000 : ℝ) ≤ ((36654478780031127323/36665000000000000000 : ℝ)+2*(1867452477599/733300000000000 : ℝ)*(20383/100000 : ℝ))^(4173/1024 : ℝ) := by
    rw [show (36654478780031127323/36665000000000000000 : ℝ)+2*(1867452477599/733300000000000 : ℝ)*(20383/100000 : ℝ)=(250187802153839/250000000000000 : ℝ) by norm_num, show 1+2*(76577753474701877/50000000000000000000 : ℝ)=(25076577753474701877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36654478780031127323/36665000000000000000 : ℝ)*(X 1 0+X 2 0)+(1867452477599/733300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (5717/100000 : ℝ)) (hi := (20383/100000 : ℝ)) (c := (36654478780031127323/36665000000000000000 : ℝ)) (alpha := (1867452477599/733300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36654478780031127323/36665000000000000000 : ℝ)*(X 0 1+X 2 1)+(1867452477599/733300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (5717/100000 : ℝ)) (hi := (20383/100000 : ℝ)) (c := (36654478780031127323/36665000000000000000 : ℝ)) (alpha := (1867452477599/733300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36654478780031127323/36665000000000000000 : ℝ)*(X 0 2+X 1 2)+(1867452477599/733300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4173/1024 : ℝ)) (lo := (5717/100000 : ℝ)) (hi := (20383/100000 : ℝ)) (c := (36654478780031127323/36665000000000000000 : ℝ)) (alpha := (1867452477599/733300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2144404711/10000000000 : ℝ)*X 0 0+(5508535889/10000000000 : ℝ)*X 0 1+(5161094669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686674769/5000000000 : ℝ)*X 1 0+(-2324955167/10000000000 : ℝ)*X 1 1+(2580548517/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686674857/5000000000 : ℝ)*X 2 0+(5161096613/10000000000 : ℝ)*X 2 1+(-1162477741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870506067/2000000000 : ℝ)*X 0 0+(251233191/625000000 : ℝ)*X 0 1+(2356289413/5000000000 : ℝ)*X 0 2+(870506067/2000000000 : ℝ)*X 1 0+(251233191/625000000 : ℝ)*X 1 1+(2356289413/5000000000 : ℝ)*X 1 2+(870506067/2000000000 : ℝ)*X 2 0+(251233191/625000000 : ℝ)*X 2 1+(2356289413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2144504107/10000000000 : ℝ)*X 0 0+(5163470559/10000000000 : ℝ)*X 0 1+(5506136313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321281053/2500000000 : ℝ)*X 1 0+(-395982701/2000000000 : ℝ)*X 1 1+(5506137111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285122489/10000000000 : ℝ)*X 2 0+(2753068407/5000000000 : ℝ)*X 2 1+(-197991629/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352727231/10000000000 : ℝ)*X 0 0+(4707842937/10000000000 : ℝ)*X 0 1+(2012257223/5000000000 : ℝ)*X 0 2+(4352727231/10000000000 : ℝ)*X 1 0+(4707842937/10000000000 : ℝ)*X 1 1+(2012257223/5000000000 : ℝ)*X 1 2+(4352727231/10000000000 : ℝ)*X 2 0+(4707842937/10000000000 : ℝ)*X 2 1+(2012257223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1154_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18320326404740139430318434033/1833250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1152917677/100000000000000 : ℝ)*(base19) + (185728749/20000000000000 : ℝ)*(base23) + (1045957/10000000000000 : ℝ)*(upper2) + (212024973/50000000000000 : ℝ)*(upper3) + (181626751/100000000000000 : ℝ)*(upper4) + (2160786141722257/100000000000000 : ℝ)*(major0) + (2160786141722257/100000000000000 : ℝ)*(major1) + (2160786141722257/100000000000000 : ℝ)*(major2) + (143910678304499/5000000000000 : ℝ)*(sp0) + (575647204028741/20000000000000 : ℝ)*(sp1) + (1439118122208819/50000000000000 : ℝ)*(sp2) + (1443324535687731/100000000000000 : ℝ)*(sp3) + (23606971403/100000000000000 : ℝ)*(sp4) + (10241583409/100000000000000 : ℝ)*(sp7) + (72166738863557/5000000000000 : ℝ)*(f.failure) + (1439118586530691/50000000000000 : ℝ)*(f.sum) + (35495879348119/4583125000000000000000000000 : ℝ)*base66 + (4003215421371921989/3666500000000000000000000000000000 : ℝ)*base68 + (12125493274513578011/3666500000000000000000000000000000 : ℝ)*base69 + (9284683966373921989/3666500000000000000000000000000000 : ℝ)*base72 + (53111360971667/36665000000000000000000000000 : ℝ)*base74 + (37181997850382078011/3666500000000000000000000000000000 : ℝ)*base75 + (21341959104166921989/3666500000000000000000000000000000 : ℝ)*base78 + (29157398519772421989/3666500000000000000000000000000000 : ℝ)*base80 + (50511765438783/36665000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3409629/500000000000000000000 : ℝ)*base89 + (3409629/500000000000000000000 : ℝ)*base91 + (3409629/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7782250306261547513066632539/916625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1420975369/100000000000000 : ℝ)*(base19) + (107667237/12500000000000 : ℝ)*(base23) + (398949179/100000000000000 : ℝ)*(upper2) + (40313453/50000000000000 : ℝ)*(upper3) + (279080583/100000000000000 : ℝ)*(upper5) + (2190854659721469/100000000000000 : ℝ)*(major0) + (2190854659721469/100000000000000 : ℝ)*(major1) + (2190854659721469/100000000000000 : ℝ)*(major2) + (114598201/500000000000 : ℝ)*(sp1) + (1168104819/100000000000000 : ℝ)*(sp2) + (1459144734158729/50000000000000 : ℝ)*(sp4) + (2918265127701889/100000000000000 : ℝ)*(sp5) + (2918287438874743/100000000000000 : ℝ)*(sp6) + (1463419568121693/100000000000000 : ℝ)*(sp7) + (1463419568121693/100000000000000 : ℝ)*(f.failure) + (1459144734158729/50000000000000 : ℝ)*(f.sum) + (43571602040137/18332500000000000000000000000 : ℝ)*base66 + (8959633746462647487/3666500000000000000000000000000000 : ℝ)*base67 + (7178385593525852513/3666500000000000000000000000000000 : ℝ)*base70 + (3197968096260647487/3666500000000000000000000000000000 : ℝ)*base71 + (32077226199591/36665000000000000000000000000 : ℝ)*base73 + (17646689817661647487/3666500000000000000000000000000000 : ℝ)*base75 + (14524508805098147487/3666500000000000000000000000000000 : ℝ)*base77 + (29168473088767147487/3666500000000000000000000000000000 : ℝ)*base79 + (144429471717319/36665000000000000000000000000 : ℝ)*base82 + (890379/10000000000000000000000 : ℝ)*base90 + (890379/10000000000000000000000 : ℝ)*base92 + (890379/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1154_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16467/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1154_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1154_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16467/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1154_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1154_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1154_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4173/1024 : ℝ) ≤ p) (hpb : p ≤ (8347/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149707897/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16467/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1154_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
