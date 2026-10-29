-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1702_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:54.793996+00:00
-- url     : https://prove2.me/submissions/f91de75b-4e5b-448d-958a-66949a019492

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
theorem support_rectangle_w1702_s0_0 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85029951/625000000 : ℝ)*x 0 + (5714143217/10000000000 : ℝ)*x 1 + (1237889197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85029951/625000000 : ℝ)^5239 ≤ (4189858971509/50000000000000 : ℝ)^4215 := by
    have hnat : (85029951 : ℕ)^5239*50000000000000^4215 ≤ 4189858971509^4215*625000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85029951 625000000 4189858971509 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5714143217/10000000000 : ℝ)^5239 ≤ (49877464823447/100000000000000 : ℝ)^4215 := by
    have hnat : (5714143217 : ℕ)^5239*100000000000000^4215 ≤ 49877464823447^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5714143217 10000000000 49877464823447 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237889197/2500000000 : ℝ)^5239 ≤ (5217852153167/12500000000000 : ℝ)^4215 := by
    have hnat : (1237889197 : ℕ)^5239*12500000000000^4215 ≤ 5217852153167^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237889197 2500000000 5217852153167 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85029951/625000000 : ℝ), (5714143217/10000000000 : ℝ), (1237889197/2500000000 : ℝ)] ![(4189858971509/50000000000000 : ℝ), (49877464823447/100000000000000 : ℝ), (5217852153167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85029951/625000000 : ℝ)|^5239 ≤ (4189858971509/50000000000000 : ℝ)^4215
        have hw : |(-85029951/625000000 : ℝ)|=(85029951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5714143217/10000000000 : ℝ)|^5239 ≤ (49877464823447/100000000000000 : ℝ)^4215
        have hw : |(5714143217/10000000000 : ℝ)|=(5714143217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1237889197/2500000000 : ℝ)|^5239 ≤ (5217852153167/12500000000000 : ℝ)^4215
        have hw : |(1237889197/2500000000 : ℝ)|=(1237889197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s0_1 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409921369/10000000000 : ℝ)*x 0 + (-354903237/2000000000 : ℝ)*x 1 + (1237889029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409921369/10000000000 : ℝ)^5239 ≤ (46598492043813/100000000000000 : ℝ)^4215 := by
    have hnat : (5409921369 : ℕ)^5239*100000000000000^4215 ≤ 46598492043813^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409921369 10000000000 46598492043813 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354903237/2000000000 : ℝ)^5239 ≤ (2914674441657/25000000000000 : ℝ)^4215 := by
    have hnat : (354903237 : ℕ)^5239*25000000000000^4215 ≤ 2914674441657^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354903237 2000000000 2914674441657 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237889029/2500000000 : ℝ)^5239 ≤ (41742810183919/100000000000000 : ℝ)^4215 := by
    have hnat : (1237889029 : ℕ)^5239*100000000000000^4215 ≤ 41742810183919^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237889029 2500000000 41742810183919 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409921369/10000000000 : ℝ), (-354903237/2000000000 : ℝ), (1237889029/2500000000 : ℝ)] ![(46598492043813/100000000000000 : ℝ), (2914674441657/25000000000000 : ℝ), (41742810183919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409921369/10000000000 : ℝ)|^5239 ≤ (46598492043813/100000000000000 : ℝ)^4215
        have hw : |(5409921369/10000000000 : ℝ)|=(5409921369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-354903237/2000000000 : ℝ)|^5239 ≤ (2914674441657/25000000000000 : ℝ)^4215
        have hw : |(-354903237/2000000000 : ℝ)|=(354903237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1237889029/2500000000 : ℝ)|^5239 ≤ (41742810183919/100000000000000 : ℝ)^4215
        have hw : |(1237889029/2500000000 : ℝ)|=(1237889029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s0_2 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081984101/2000000000 : ℝ)*x 0 + (4951556843/10000000000 : ℝ)*x 1 + (-1774516383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081984101/2000000000 : ℝ)^5239 ≤ (23299241396867/50000000000000 : ℝ)^4215 := by
    have hnat : (1081984101 : ℕ)^5239*50000000000000^4215 ≤ 23299241396867^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081984101 2000000000 23299241396867 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4951556843/10000000000 : ℝ)^5239 ≤ (41742817801643/100000000000000 : ℝ)^4215 := by
    have hnat : (4951556843 : ℕ)^5239*100000000000000^4215 ≤ 41742817801643^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4951556843 10000000000 41742817801643 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1774516383/10000000000 : ℝ)^5239 ≤ (11658699383539/100000000000000 : ℝ)^4215 := by
    have hnat : (1774516383 : ℕ)^5239*100000000000000^4215 ≤ 11658699383539^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774516383 10000000000 11658699383539 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081984101/2000000000 : ℝ), (4951556843/10000000000 : ℝ), (-1774516383/10000000000 : ℝ)] ![(23299241396867/50000000000000 : ℝ), (41742817801643/100000000000000 : ℝ), (11658699383539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081984101/2000000000 : ℝ)|^5239 ≤ (23299241396867/50000000000000 : ℝ)^4215
        have hw : |(1081984101/2000000000 : ℝ)|=(1081984101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4951556843/10000000000 : ℝ)|^5239 ≤ (41742817801643/100000000000000 : ℝ)^4215
        have hw : |(4951556843/10000000000 : ℝ)|=(4951556843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1774516383/10000000000 : ℝ)|^5239 ≤ (11658699383539/100000000000000 : ℝ)^4215
        have hw : |(-1774516383/10000000000 : ℝ)|=(1774516383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s0_3 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4046324707/10000000000 : ℝ)*x 0 + (3054219491/10000000000 : ℝ)*x 1 + (522482881/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4046324707/10000000000 : ℝ)^5239 ≤ (16239375821989/50000000000000 : ℝ)^4215 := by
    have hnat : (4046324707 : ℕ)^5239*50000000000000^4215 ≤ 16239375821989^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4046324707 10000000000 16239375821989 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3054219491/10000000000 : ℝ)^5239 ≤ (22896070004959/100000000000000 : ℝ)^4215 := by
    have hnat : (3054219491 : ℕ)^5239*100000000000000^4215 ≤ 22896070004959^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3054219491 10000000000 22896070004959 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522482881/1000000000 : ℝ)^5239 ≤ (11156294583167/25000000000000 : ℝ)^4215 := by
    have hnat : (522482881 : ℕ)^5239*25000000000000^4215 ≤ 11156294583167^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522482881 1000000000 11156294583167 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4046324707/10000000000 : ℝ), (3054219491/10000000000 : ℝ), (522482881/1000000000 : ℝ)] ![(16239375821989/50000000000000 : ℝ), (22896070004959/100000000000000 : ℝ), (11156294583167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4046324707/10000000000 : ℝ)|^5239 ≤ (16239375821989/50000000000000 : ℝ)^4215
        have hw : |(4046324707/10000000000 : ℝ)|=(4046324707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3054219491/10000000000 : ℝ)|^5239 ≤ (22896070004959/100000000000000 : ℝ)^4215
        have hw : |(3054219491/10000000000 : ℝ)|=(3054219491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522482881/1000000000 : ℝ)|^5239 ≤ (11156294583167/25000000000000 : ℝ)^4215
        have hw : |(522482881/1000000000 : ℝ)|=(522482881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s0_4 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-272455513/2000000000 : ℝ)*x 0 + (2485229657/5000000000 : ℝ)*x 1 + (28473007/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272455513/2000000000 : ℝ)^5239 ≤ (4196743940603/50000000000000 : ℝ)^4215 := by
    have hnat : (272455513 : ℕ)^5239*50000000000000^4215 ≤ 4196743940603^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272455513 2000000000 4196743940603 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2485229657/5000000000 : ℝ)^5239 ≤ (4194097531369/10000000000000 : ℝ)^4215 := by
    have hnat : (2485229657 : ℕ)^5239*10000000000000^4215 ≤ 4194097531369^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2485229657 5000000000 4194097531369 10000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28473007/50000000 : ℝ)^5239 ≤ (49665536792171/100000000000000 : ℝ)^4215 := by
    have hnat : (28473007 : ℕ)^5239*100000000000000^4215 ≤ 49665536792171^4215*50000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28473007 50000000 49665536792171 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272455513/2000000000 : ℝ), (2485229657/5000000000 : ℝ), (28473007/50000000 : ℝ)] ![(4196743940603/50000000000000 : ℝ), (4194097531369/10000000000000 : ℝ), (49665536792171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272455513/2000000000 : ℝ)|^5239 ≤ (4196743940603/50000000000000 : ℝ)^4215
        have hw : |(-272455513/2000000000 : ℝ)|=(272455513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2485229657/5000000000 : ℝ)|^5239 ≤ (4194097531369/10000000000000 : ℝ)^4215
        have hw : |(2485229657/5000000000 : ℝ)|=(2485229657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28473007/50000000 : ℝ)|^5239 ≤ (49665536792171/100000000000000 : ℝ)^4215
        have hw : |(28473007/50000000 : ℝ)|=(28473007/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s0_5 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650385921/1250000000 : ℝ)*x 0 + (-1031471347/10000000000 : ℝ)*x 1 + (569460133/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650385921/1250000000 : ℝ)^5239 ≤ (11098622283833/25000000000000 : ℝ)^4215 := by
    have hnat : (650385921 : ℕ)^5239*25000000000000^4215 ≤ 11098622283833^4215*1250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650385921 1250000000 11098622283833 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031471347/10000000000 : ℝ)^5239 ≤ (742496852103/12500000000000 : ℝ)^4215 := by
    have hnat : (1031471347 : ℕ)^5239*12500000000000^4215 ≤ 742496852103^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031471347 10000000000 742496852103 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569460133/1000000000 : ℝ)^5239 ≤ (12416384008337/25000000000000 : ℝ)^4215 := by
    have hnat : (569460133 : ℕ)^5239*25000000000000^4215 ≤ 12416384008337^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569460133 1000000000 12416384008337 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650385921/1250000000 : ℝ), (-1031471347/10000000000 : ℝ), (569460133/1000000000 : ℝ)] ![(11098622283833/25000000000000 : ℝ), (742496852103/12500000000000 : ℝ), (12416384008337/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650385921/1250000000 : ℝ)|^5239 ≤ (11098622283833/25000000000000 : ℝ)^4215
        have hw : |(650385921/1250000000 : ℝ)|=(650385921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031471347/10000000000 : ℝ)|^5239 ≤ (742496852103/12500000000000 : ℝ)^4215
        have hw : |(-1031471347/10000000000 : ℝ)|=(1031471347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569460133/1000000000 : ℝ)|^5239 ≤ (12416384008337/25000000000000 : ℝ)^4215
        have hw : |(569460133/1000000000 : ℝ)|=(569460133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s0_6 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650385919/1250000000 : ℝ)*x 0 + (569460167/1000000000 : ℝ)*x 1 + (-128933857/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650385919/1250000000 : ℝ)^5239 ≤ (44394488965649/100000000000000 : ℝ)^4215 := by
    have hnat : (650385919 : ℕ)^5239*100000000000000^4215 ≤ 44394488965649^4215*1250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650385919 1250000000 44394488965649 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569460167/1000000000 : ℝ)^5239 ≤ (49665539719061/100000000000000 : ℝ)^4215 := by
    have hnat : (569460167 : ℕ)^5239*100000000000000^4215 ≤ 49665539719061^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569460167 1000000000 49665539719061 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128933857/1250000000 : ℝ)^5239 ≤ (1187994260471/20000000000000 : ℝ)^4215 := by
    have hnat : (128933857 : ℕ)^5239*20000000000000^4215 ≤ 1187994260471^4215*1250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128933857 1250000000 1187994260471 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650385919/1250000000 : ℝ), (569460167/1000000000 : ℝ), (-128933857/1250000000 : ℝ)] ![(44394488965649/100000000000000 : ℝ), (49665539719061/100000000000000 : ℝ), (1187994260471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650385919/1250000000 : ℝ)|^5239 ≤ (44394488965649/100000000000000 : ℝ)^4215
        have hw : |(650385919/1250000000 : ℝ)|=(650385919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569460167/1000000000 : ℝ)|^5239 ≤ (49665539719061/100000000000000 : ℝ)^4215
        have hw : |(569460167/1000000000 : ℝ)|=(569460167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128933857/1250000000 : ℝ)|^5239 ≤ (1187994260471/20000000000000 : ℝ)^4215
        have hw : |(-128933857/1250000000 : ℝ)|=(128933857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s0_7 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4051440623/10000000000 : ℝ)*x 0 + (2585512541/5000000000 : ℝ)*x 1 + (155492071/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4051440623/10000000000 : ℝ)^5239 ≤ (32529799733663/100000000000000 : ℝ)^4215 := by
    have hnat : (4051440623 : ℕ)^5239*100000000000000^4215 ≤ 32529799733663^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051440623 10000000000 32529799733663 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585512541/5000000000 : ℝ)^5239 ≤ (5506839646597/12500000000000 : ℝ)^4215 := by
    have hnat : (2585512541 : ℕ)^5239*12500000000000^4215 ≤ 5506839646597^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585512541 5000000000 5506839646597 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155492071/500000000 : ℝ)^5239 ≤ (23415483066581/100000000000000 : ℝ)^4215 := by
    have hnat : (155492071 : ℕ)^5239*100000000000000^4215 ≤ 23415483066581^4215*500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155492071 500000000 23415483066581 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4051440623/10000000000 : ℝ), (2585512541/5000000000 : ℝ), (155492071/500000000 : ℝ)] ![(32529799733663/100000000000000 : ℝ), (5506839646597/12500000000000 : ℝ), (23415483066581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4051440623/10000000000 : ℝ)|^5239 ≤ (32529799733663/100000000000000 : ℝ)^4215
        have hw : |(4051440623/10000000000 : ℝ)|=(4051440623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585512541/5000000000 : ℝ)|^5239 ≤ (5506839646597/12500000000000 : ℝ)^4215
        have hw : |(2585512541/5000000000 : ℝ)|=(2585512541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(155492071/500000000 : ℝ)|^5239 ≤ (23415483066581/100000000000000 : ℝ)^4215
        have hw : |(155492071/500000000 : ℝ)|=(155492071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1702_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1453/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11097/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5231/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5231 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5231*1^1024 ≤ 0^1024*1^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5231/1024 : ℝ) ≤ (231794907396734931/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5231 ≤ (231794907396734931/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5231*25000000000000000000^1024 ≤ 231794907396734931^1024*5^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 231794907396734931 25000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (231794907396734931/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5231 := by
      have hnat : (1 : ℕ)^1024*1^5231 ≤ 1^5231*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25231794907396734931/25000000000000000000 : ℝ) ≤ (5009041404099209/5000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (25231794907396734931/25000000000000000000 : ℝ)^1024 ≤ (5009041404099209/5000000000000000 : ℝ)^5231 := by
      have hnat : (25231794907396734931 : ℕ)^1024*5000000000000000^5231 ≤ 5009041404099209^5231*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25231794907396734931 25000000000000000000 5009041404099209 5000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009041404099209/5000000000000000 : ℝ)) (X := (25231794907396734931/25000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12731794907396734931/12500000000000000000 : ℝ) ≤ (2509041404099209/2500000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (12731794907396734931/12500000000000000000 : ℝ)^1024 ≤ (2509041404099209/2500000000000000 : ℝ)^5231 := by
      have hnat : (12731794907396734931 : ℕ)^1024*2500000000000000^5231 ≤ 2509041404099209^5231*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12731794907396734931 12500000000000000000 2509041404099209 2500000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509041404099209/2500000000000000 : ℝ)) (X := (12731794907396734931/12500000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9041404099209/2000000000000000 : ℝ)*(0 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9041404099209/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(231794907396734931/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9041404099209/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5231/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9041404099209/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5009041404099209/5000000000000000 : ℝ) by norm_num, show 1+(231794907396734931/25000000000000000000 : ℝ)+(0 : ℝ)=(25231794907396734931/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(231794907396734931/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9041404099209/2000000000000000 : ℝ)*(2/5 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9041404099209/2000000000000000 : ℝ)*(2/5 : ℝ)=(2509041404099209/2500000000000000 : ℝ) by norm_num, show 1+2*(231794907396734931/25000000000000000000 : ℝ)=(12731794907396734931/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9041404099209/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9041404099209/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9041404099209/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9041404099209/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9041404099209/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9041404099209/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85029951/625000000 : ℝ)*X 0 0+(5714143217/10000000000 : ℝ)*X 0 1+(1237889197/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5409921369/10000000000 : ℝ)*X 1 0+(-354903237/2000000000 : ℝ)*X 1 1+(1237889029/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1081984101/2000000000 : ℝ)*X 2 0+(4951556843/10000000000 : ℝ)*X 2 1+(-1774516383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4046324707/10000000000 : ℝ)*X 0 0+(3054219491/10000000000 : ℝ)*X 0 1+(522482881/1000000000 : ℝ)*X 0 2+(4046324707/10000000000 : ℝ)*X 1 0+(3054219491/10000000000 : ℝ)*X 1 1+(522482881/1000000000 : ℝ)*X 1 2+(4046324707/10000000000 : ℝ)*X 2 0+(3054219491/10000000000 : ℝ)*X 2 1+(522482881/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272455513/2000000000 : ℝ)*X 0 0+(2485229657/5000000000 : ℝ)*X 0 1+(28473007/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((650385921/1250000000 : ℝ)*X 1 0+(-1031471347/10000000000 : ℝ)*X 1 1+(569460133/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((650385919/1250000000 : ℝ)*X 2 0+(569460167/1000000000 : ℝ)*X 2 1+(-128933857/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4051440623/10000000000 : ℝ)*X 0 0+(2585512541/5000000000 : ℝ)*X 0 1+(155492071/500000000 : ℝ)*X 0 2+(4051440623/10000000000 : ℝ)*X 1 0+(2585512541/5000000000 : ℝ)*X 1 1+(155492071/500000000 : ℝ)*X 1 2+(4051440623/10000000000 : ℝ)*X 2 0+(2585512541/5000000000 : ℝ)*X 2 1+(155492071/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8113823181650990637987/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17362763/10000000000000 : ℝ)*(base1) + (1333742511/100000000000000 : ℝ)*(base19) + (1124313853/100000000000000 : ℝ)*(base23) + (28794221/12500000000000 : ℝ)*(upper3) + (107815819/100000000000000 : ℝ)*(upper5) + (44300956998569/5000000000000 : ℝ)*(major0) + (44300956998569/5000000000000 : ℝ)*(major1) + (44300956998569/5000000000000 : ℝ)*(major2) + (204895574751/15625000000 : ℝ)*(sp0) + (655666894859207/50000000000000 : ℝ)*(sp1) + (1311333999147073/100000000000000 : ℝ)*(sp2) + (460701274842789/100000000000000 : ℝ)*(sp3) + (723736431/20000000000000 : ℝ)*(sp4) + (1491642789/100000000000000 : ℝ)*(sp7) + (57587867514151/12500000000000 : ℝ)*(f.failure) + (655667561730463/50000000000000 : ℝ)*(f.sum) + (7356895056921/5000000000000000000000000000 : ℝ)*base65 + (92566101361921/10000000000000000000000000000 : ℝ)*base67 + (1142430331921/10000000000000000000000000000 : ℝ)*base69 + (89168805671921/10000000000000000000000000000 : ℝ)*base71 + (7431229496921/5000000000000000000000000000 : ℝ)*base73 + (83153832091921/10000000000000000000000000000 : ℝ)*base75 + (65748374681921/10000000000000000000000000000 : ℝ)*base77 + (14347700671921/10000000000000000000000000000 : ℝ)*base79 + (17603625523079/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (535479/156250000000000000000 : ℝ)*base90 + (535479/156250000000000000000 : ℝ)*base92 + (535479/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25321059115965894583641/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2034691213/100000000000000 : ℝ)*(base19) + (535813401/25000000000000 : ℝ)*(base23) + (17290547/50000000000000 : ℝ)*(upper2) + (41836821/12500000000000 : ℝ)*(upper3) + (155344369/50000000000000 : ℝ)*(upper5) + (29157851602043/3125000000000 : ℝ)*(major0) + (29157851602043/3125000000000 : ℝ)*(major1) + (29157851602043/3125000000000 : ℝ)*(major2) + (894384517/12500000000000 : ℝ)*(sp1) + (1040123849/12500000000000 : ℝ)*(sp2) + (172618003544191/12500000000000 : ℝ)*(sp4) + (69046741929309/5000000000000 : ℝ)*(sp5) + (345233391027283/25000000000000 : ℝ)*(sp6) + (485158204085921/100000000000000 : ℝ)*(sp7) + (485158204085921/100000000000000 : ℝ)*(f.failure) + (172618003544191/12500000000000 : ℝ)*(f.sum) + (247387217993/195312500000000000000000000 : ℝ)*base66 + (21377230378513/6250000000000000000000000000 : ℝ)*base68 + (27014459791013/6250000000000000000000000000 : ℝ)*base70 + (48383873459763/6250000000000000000000000000 : ℝ)*base72 + (2820243734763/3125000000000000000000000000 : ℝ)*base74 + (73016509641013/6250000000000000000000000000 : ℝ)*base76 + (25309898459763/6250000000000000000000000000 : ℝ)*base78 + (11906482278513/6250000000000000000000000000 : ℝ)*base80 + (4171558078513/3125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13756191/1250000000000000000000 : ℝ)*base89 + (13756191/1250000000000000000000 : ℝ)*base91 + (13756191/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1702_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1453/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11097/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1702_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1702_s1_0 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1437190567/10000000000 : ℝ)*x 0 + (343295973/625000000 : ℝ)*x 1 + (320161107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1437190567/10000000000 : ℝ)^5239 ≤ (2242742049761/25000000000000 : ℝ)^4215 := by
    have hnat : (1437190567 : ℕ)^5239*25000000000000^4215 ≤ 2242742049761^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437190567 10000000000 2242742049761 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343295973/625000000 : ℝ)^5239 ≤ (2374337616391/5000000000000 : ℝ)^4215 := by
    have hnat : (343295973 : ℕ)^5239*5000000000000^4215 ≤ 2374337616391^4215*625000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343295973 625000000 2374337616391 5000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320161107/625000000 : ℝ)^5239 ≤ (43542279454907/100000000000000 : ℝ)^4215 := by
    have hnat : (320161107 : ℕ)^5239*100000000000000^4215 ≤ 43542279454907^4215*625000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320161107 625000000 43542279454907 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1437190567/10000000000 : ℝ), (343295973/625000000 : ℝ), (320161107/625000000 : ℝ)] ![(2242742049761/25000000000000 : ℝ), (2374337616391/5000000000000 : ℝ), (43542279454907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1437190567/10000000000 : ℝ)|^5239 ≤ (2242742049761/25000000000000 : ℝ)^4215
        have hw : |(-1437190567/10000000000 : ℝ)|=(1437190567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343295973/625000000 : ℝ)|^5239 ≤ (2374337616391/5000000000000 : ℝ)^4215
        have hw : |(343295973/625000000 : ℝ)|=(343295973/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320161107/625000000 : ℝ)|^5239 ≤ (43542279454907/100000000000000 : ℝ)^4215
        have hw : |(320161107/625000000 : ℝ)|=(320161107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s1_1 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350939417/10000000000 : ℝ)*x 0 + (-81496213/500000000 : ℝ)*x 1 + (5122576969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350939417/10000000000 : ℝ)^5239 ≤ (4596786332799/10000000000000 : ℝ)^4215 := by
    have hnat : (5350939417 : ℕ)^5239*10000000000000^4215 ≤ 4596786332799^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350939417 10000000000 4596786332799 10000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81496213/500000000 : ℝ)^5239 ≤ (10489865053299/100000000000000 : ℝ)^4215 := by
    have hnat : (81496213 : ℕ)^5239*100000000000000^4215 ≤ 10489865053299^4215*500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81496213 500000000 10489865053299 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5122576969/10000000000 : ℝ)^5239 ≤ (43542271605041/100000000000000 : ℝ)^4215 := by
    have hnat : (5122576969 : ℕ)^5239*100000000000000^4215 ≤ 43542271605041^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5122576969 10000000000 43542271605041 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350939417/10000000000 : ℝ), (-81496213/500000000 : ℝ), (5122576969/10000000000 : ℝ)] ![(4596786332799/10000000000000 : ℝ), (10489865053299/100000000000000 : ℝ), (43542271605041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350939417/10000000000 : ℝ)|^5239 ≤ (4596786332799/10000000000000 : ℝ)^4215
        have hw : |(5350939417/10000000000 : ℝ)|=(5350939417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81496213/500000000 : ℝ)|^5239 ≤ (10489865053299/100000000000000 : ℝ)^4215
        have hw : |(-81496213/500000000 : ℝ)|=(81496213/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5122576969/10000000000 : ℝ)|^5239 ≤ (43542271605041/100000000000000 : ℝ)^4215
        have hw : |(5122576969/10000000000 : ℝ)|=(5122576969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s1_2 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267546907/500000000 : ℝ)*x 0 + (1280644521/2500000000 : ℝ)*x 1 + (-407481123/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267546907/500000000 : ℝ)^5239 ≤ (45967849692649/100000000000000 : ℝ)^4215 := by
    have hnat : (267546907 : ℕ)^5239*100000000000000^4215 ≤ 45967849692649^4215*500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267546907 500000000 45967849692649 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1280644521/2500000000 : ℝ)^5239 ≤ (21771141692561/50000000000000 : ℝ)^4215 := by
    have hnat : (1280644521 : ℕ)^5239*50000000000000^4215 ≤ 21771141692561^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280644521 2500000000 21771141692561 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407481123/2500000000 : ℝ)^5239 ≤ (5244933454571/50000000000000 : ℝ)^4215 := by
    have hnat : (407481123 : ℕ)^5239*50000000000000^4215 ≤ 5244933454571^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407481123 2500000000 5244933454571 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267546907/500000000 : ℝ), (1280644521/2500000000 : ℝ), (-407481123/2500000000 : ℝ)] ![(45967849692649/100000000000000 : ℝ), (21771141692561/50000000000000 : ℝ), (5244933454571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267546907/500000000 : ℝ)|^5239 ≤ (45967849692649/100000000000000 : ℝ)^4215
        have hw : |(267546907/500000000 : ℝ)|=(267546907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1280644521/2500000000 : ℝ)|^5239 ≤ (21771141692561/50000000000000 : ℝ)^4215
        have hw : |(1280644521/2500000000 : ℝ)|=(1280644521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407481123/2500000000 : ℝ)|^5239 ≤ (5244933454571/50000000000000 : ℝ)^4215
        have hw : |(-407481123/2500000000 : ℝ)|=(407481123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s1_3 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1027946801/2500000000 : ℝ)*x 0 + (721354139/2000000000 : ℝ)*x 1 + (4660380007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027946801/2500000000 : ℝ)^5239 ≤ (828328334287/2500000000000 : ℝ)^4215 := by
    have hnat : (1027946801 : ℕ)^5239*2500000000000^4215 ≤ 828328334287^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027946801 2500000000 828328334287 2500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721354139/2000000000 : ℝ)^5239 ≤ (14076480495309/50000000000000 : ℝ)^4215 := by
    have hnat : (721354139 : ℕ)^5239*50000000000000^4215 ≤ 14076480495309^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721354139 2000000000 14076480495309 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4660380007/10000000000 : ℝ)^5239 ≤ (38713905625821/100000000000000 : ℝ)^4215 := by
    have hnat : (4660380007 : ℕ)^5239*100000000000000^4215 ≤ 38713905625821^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4660380007 10000000000 38713905625821 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1027946801/2500000000 : ℝ), (721354139/2000000000 : ℝ), (4660380007/10000000000 : ℝ)] ![(828328334287/2500000000000 : ℝ), (14076480495309/50000000000000 : ℝ), (38713905625821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1027946801/2500000000 : ℝ)|^5239 ≤ (828328334287/2500000000000 : ℝ)^4215
        have hw : |(1027946801/2500000000 : ℝ)|=(1027946801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(721354139/2000000000 : ℝ)|^5239 ≤ (14076480495309/50000000000000 : ℝ)^4215
        have hw : |(721354139/2000000000 : ℝ)|=(721354139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4660380007/10000000000 : ℝ)|^5239 ≤ (38713905625821/100000000000000 : ℝ)^4215
        have hw : |(4660380007/10000000000 : ℝ)|=(4660380007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s1_4 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1437393857/10000000000 : ℝ)*x 0 + (205081303/400000000 : ℝ)*x 1 + (5488207883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1437393857/10000000000 : ℝ)^5239 ≤ (2243136361099/25000000000000 : ℝ)^4215 := by
    have hnat : (1437393857 : ℕ)^5239*25000000000000^4215 ≤ 2243136361099^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437393857 10000000000 2243136361099 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205081303/400000000 : ℝ)^5239 ≤ (10897337619633/25000000000000 : ℝ)^4215 := by
    have hnat : (205081303 : ℕ)^5239*25000000000000^4215 ≤ 10897337619633^4215*400000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205081303 400000000 10897337619633 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488207883/10000000000 : ℝ)^5239 ≤ (47438104068621/100000000000000 : ℝ)^4215 := by
    have hnat : (5488207883 : ℕ)^5239*100000000000000^4215 ≤ 47438104068621^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488207883 10000000000 47438104068621 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1437393857/10000000000 : ℝ), (205081303/400000000 : ℝ), (5488207883/10000000000 : ℝ)] ![(2243136361099/25000000000000 : ℝ), (10897337619633/25000000000000 : ℝ), (47438104068621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1437393857/10000000000 : ℝ)|^5239 ≤ (2243136361099/25000000000000 : ℝ)^4215
        have hw : |(-1437393857/10000000000 : ℝ)|=(1437393857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205081303/400000000 : ℝ)|^5239 ≤ (10897337619633/25000000000000 : ℝ)^4215
        have hw : |(205081303/400000000 : ℝ)|=(205081303/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488207883/10000000000 : ℝ)|^5239 ≤ (47438104068621/100000000000000 : ℝ)^4215
        have hw : |(5488207883/10000000000 : ℝ)|=(5488207883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s1_5 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251840507/10000000000 : ℝ)*x 0 + (-1264293791/10000000000 : ℝ)*x 1 + (5488207621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251840507/10000000000 : ℝ)^5239 ≤ (44912112905699/100000000000000 : ℝ)^4215 := by
    have hnat : (5251840507 : ℕ)^5239*100000000000000^4215 ≤ 44912112905699^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251840507 10000000000 44912112905699 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1264293791/10000000000 : ℝ)^5239 ≤ (3824892911961/50000000000000 : ℝ)^4215 := by
    have hnat : (1264293791 : ℕ)^5239*50000000000000^4215 ≤ 3824892911961^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264293791 10000000000 3824892911961 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5488207621/10000000000 : ℝ)^5239 ≤ (11859525313453/25000000000000 : ℝ)^4215 := by
    have hnat : (5488207621 : ℕ)^5239*25000000000000^4215 ≤ 11859525313453^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488207621 10000000000 11859525313453 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251840507/10000000000 : ℝ), (-1264293791/10000000000 : ℝ), (5488207621/10000000000 : ℝ)] ![(44912112905699/100000000000000 : ℝ), (3824892911961/50000000000000 : ℝ), (11859525313453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251840507/10000000000 : ℝ)|^5239 ≤ (44912112905699/100000000000000 : ℝ)^4215
        have hw : |(5251840507/10000000000 : ℝ)|=(5251840507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1264293791/10000000000 : ℝ)|^5239 ≤ (3824892911961/50000000000000 : ℝ)^4215
        have hw : |(-1264293791/10000000000 : ℝ)|=(1264293791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5488207621/10000000000 : ℝ)|^5239 ≤ (11859525313453/25000000000000 : ℝ)^4215
        have hw : |(5488207621/10000000000 : ℝ)|=(5488207621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s1_6 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328240043/625000000 : ℝ)*x 0 + (343012987/625000000 : ℝ)*x 1 + (-1264293291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328240043/625000000 : ℝ)^5239 ≤ (22456057414797/50000000000000 : ℝ)^4215 := by
    have hnat : (328240043 : ℕ)^5239*50000000000000^4215 ≤ 22456057414797^4215*625000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328240043 625000000 22456057414797 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343012987/625000000 : ℝ)^5239 ≤ (23719051545479/50000000000000 : ℝ)^4215 := by
    have hnat : (343012987 : ℕ)^5239*50000000000000^4215 ≤ 23719051545479^4215*625000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343012987 625000000 23719051545479 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1264293291/10000000000 : ℝ)^5239 ≤ (3824891031813/50000000000000 : ℝ)^4215 := by
    have hnat : (1264293291 : ℕ)^5239*50000000000000^4215 ≤ 3824891031813^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264293291 10000000000 3824891031813 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328240043/625000000 : ℝ), (343012987/625000000 : ℝ), (-1264293291/10000000000 : ℝ)] ![(22456057414797/50000000000000 : ℝ), (23719051545479/50000000000000 : ℝ), (3824891031813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328240043/625000000 : ℝ)|^5239 ≤ (22456057414797/50000000000000 : ℝ)^4215
        have hw : |(328240043/625000000 : ℝ)|=(328240043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(343012987/625000000 : ℝ)|^5239 ≤ (23719051545479/50000000000000 : ℝ)^4215
        have hw : |(343012987/625000000 : ℝ)|=(343012987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1264293291/10000000000 : ℝ)|^5239 ≤ (3824891031813/50000000000000 : ℝ)^4215
        have hw : |(-1264293291/10000000000 : ℝ)|=(1264293291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s1_7 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (205618333/500000000 : ℝ)*x 0 + (116192491/250000000 : ℝ)*x 1 + (3619657403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205618333/500000000 : ℝ)^5239 ≤ (16569468573429/50000000000000 : ℝ)^4215 := by
    have hnat : (205618333 : ℕ)^5239*50000000000000^4215 ≤ 16569468573429^4215*500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205618333 500000000 16569468573429 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116192491/250000000 : ℝ)^5239 ≤ (38583022204581/100000000000000 : ℝ)^4215 := by
    have hnat : (116192491 : ℕ)^5239*100000000000000^4215 ≤ 38583022204581^4215*250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116192491 250000000 38583022204581 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3619657403/10000000000 : ℝ)^5239 ≤ (28278040632627/100000000000000 : ℝ)^4215 := by
    have hnat : (3619657403 : ℕ)^5239*100000000000000^4215 ≤ 28278040632627^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3619657403 10000000000 28278040632627 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205618333/500000000 : ℝ), (116192491/250000000 : ℝ), (3619657403/10000000000 : ℝ)] ![(16569468573429/50000000000000 : ℝ), (38583022204581/100000000000000 : ℝ), (28278040632627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205618333/500000000 : ℝ)|^5239 ≤ (16569468573429/50000000000000 : ℝ)^4215
        have hw : |(205618333/500000000 : ℝ)|=(205618333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116192491/250000000 : ℝ)|^5239 ≤ (38583022204581/100000000000000 : ℝ)^4215
        have hw : |(116192491/250000000 : ℝ)|=(116192491/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3619657403/10000000000 : ℝ)|^5239 ≤ (28278040632627/100000000000000 : ℝ)^4215
        have hw : |(3619657403/10000000000 : ℝ)|=(3619657403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1702_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1453/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1203/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8759/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1453/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1453/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1453/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1453/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1453/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1453/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1453/25000 : ℝ) ^ (5231/1024 : ℝ) ≤ (24358630010691/50000000000000000000 : ℝ) := by
    have hpowers : (1453/25000 : ℝ)^5231 ≤ (24358630010691/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1453 : ℕ)^5231*50000000000000000000^1024 ≤ 24358630010691^1024*25000^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1453 25000 24358630010691 50000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1453/25000 : ℝ)) (X := (24358630010691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11097/50000 : ℝ) ^ (5231/1024 : ℝ) ≤ (9148309789730237/20000000000000000000 : ℝ) := by
    have hpowers : (11097/50000 : ℝ)^5231 ≤ (9148309789730237/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11097 : ℕ)^5231*20000000000000000000^1024 ≤ 9148309789730237^1024*50000^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11097 50000 9148309789730237 20000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11097/50000 : ℝ)) (X := (9148309789730237/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000024358630010691/25000000000000000000 : ℝ) ≤ (5000000953669561/5000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (25000024358630010691/25000000000000000000 : ℝ)^1024 ≤ (5000000953669561/5000000000000000 : ℝ)^5231 := by
      have hnat : (25000024358630010691 : ℕ)^1024*5000000000000000^5231 ≤ 5000000953669561^5231*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000024358630010691 25000000000000000000 5000000953669561 5000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000953669561/5000000000000000 : ℝ)) (X := (25000024358630010691/25000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045790266208672567/100000000000000000000 : ℝ) ≤ (5000448103623903/5000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (100045790266208672567/100000000000000000000 : ℝ)^1024 ≤ (5000448103623903/5000000000000000 : ℝ)^5231 := by
      have hnat : (100045790266208672567 : ℕ)^1024*5000000000000000^5231 ≤ 5000448103623903^5231*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045790266208672567 100000000000000000000 5000448103623903 5000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000448103623903/5000000000000000 : ℝ)) (X := (100045790266208672567/100000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009148309789730237/10000000000000000000 : ℝ) ≤ (1000179050715649/1000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (10009148309789730237/10000000000000000000 : ℝ)^1024 ≤ (1000179050715649/1000000000000000 : ℝ)^5231 := by
      have hnat : (10009148309789730237 : ℕ)^1024*1000000000000000^5231 ≤ 1000179050715649^5231*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009148309789730237 10000000000000000000 1000179050715649 1000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000179050715649/1000000000000000 : ℝ)) (X := (10009148309789730237/10000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24358630010691/50000000000000000000 : ℝ) ≤ ((40952408975972738447/40955000000000000000 : ℝ)+2*(223574977171/409550000000000 : ℝ)*(1453/25000 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (40952408975972738447/40955000000000000000 : ℝ)+2*(223574977171/409550000000000 : ℝ)*(1453/25000 : ℝ)=(5000000953669561/5000000000000000 : ℝ) by norm_num, show 1+2*(24358630010691/50000000000000000000 : ℝ)=(25000024358630010691/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9148309789730237/20000000000000000000 : ℝ)+(24358630010691/50000000000000000000 : ℝ) ≤ ((40952408975972738447/40955000000000000000 : ℝ)+(223574977171/409550000000000 : ℝ)*((11097/50000 : ℝ)+(1453/25000 : ℝ)))^(5231/1024 : ℝ) := by
    rw [show (40952408975972738447/40955000000000000000 : ℝ)+(223574977171/409550000000000 : ℝ)*((11097/50000 : ℝ)+(1453/25000 : ℝ))=(5000448103623903/5000000000000000 : ℝ) by norm_num, show 1+(9148309789730237/20000000000000000000 : ℝ)+(24358630010691/50000000000000000000 : ℝ)=(100045790266208672567/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9148309789730237/20000000000000000000 : ℝ) ≤ ((40952408975972738447/40955000000000000000 : ℝ)+2*(223574977171/409550000000000 : ℝ)*(11097/50000 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (40952408975972738447/40955000000000000000 : ℝ)+2*(223574977171/409550000000000 : ℝ)*(11097/50000 : ℝ)=(1000179050715649/1000000000000000 : ℝ) by norm_num, show 1+2*(9148309789730237/20000000000000000000 : ℝ)=(10009148309789730237/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40952408975972738447/40955000000000000000 : ℝ)*(X 1 0+X 2 0)+(223574977171/409550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1453/25000 : ℝ)) (hi := (11097/50000 : ℝ)) (c := (40952408975972738447/40955000000000000000 : ℝ)) (alpha := (223574977171/409550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40952408975972738447/40955000000000000000 : ℝ)*(X 0 1+X 2 1)+(223574977171/409550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1453/25000 : ℝ)) (hi := (11097/50000 : ℝ)) (c := (40952408975972738447/40955000000000000000 : ℝ)) (alpha := (223574977171/409550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40952408975972738447/40955000000000000000 : ℝ)*(X 0 2+X 1 2)+(223574977171/409550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1453/25000 : ℝ)) (hi := (11097/50000 : ℝ)) (c := (40952408975972738447/40955000000000000000 : ℝ)) (alpha := (223574977171/409550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1437190567/10000000000 : ℝ)*X 0 0+(343295973/625000000 : ℝ)*X 0 1+(320161107/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350939417/10000000000 : ℝ)*X 1 0+(-81496213/500000000 : ℝ)*X 1 1+(5122576969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267546907/500000000 : ℝ)*X 2 0+(1280644521/2500000000 : ℝ)*X 2 1+(-407481123/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1027946801/2500000000 : ℝ)*X 0 0+(721354139/2000000000 : ℝ)*X 0 1+(4660380007/10000000000 : ℝ)*X 0 2+(1027946801/2500000000 : ℝ)*X 1 0+(721354139/2000000000 : ℝ)*X 1 1+(4660380007/10000000000 : ℝ)*X 1 2+(1027946801/2500000000 : ℝ)*X 2 0+(721354139/2000000000 : ℝ)*X 2 1+(4660380007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1437393857/10000000000 : ℝ)*X 0 0+(205081303/400000000 : ℝ)*X 0 1+(5488207883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251840507/10000000000 : ℝ)*X 1 0+(-1264293791/10000000000 : ℝ)*X 1 1+(5488207621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328240043/625000000 : ℝ)*X 2 0+(343012987/625000000 : ℝ)*X 2 1+(-1264293291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((205618333/500000000 : ℝ)*X 0 0+(116192491/250000000 : ℝ)*X 0 1+(3619657403/10000000000 : ℝ)*X 0 2+(205618333/500000000 : ℝ)*X 1 0+(116192491/250000000 : ℝ)*X 1 1+(3619657403/10000000000 : ℝ)*X 1 2+(205618333/500000000 : ℝ)*X 2 0+(116192491/250000000 : ℝ)*X 2 1+(3619657403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7050617113465868225943303609/511937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (482503827/25000000000000 : ℝ)*(base19) + (143015893/12500000000000 : ℝ)*(base23) + (75532831/100000000000000 : ℝ)*(lower2) + (6018287/1562500000000 : ℝ)*(upper3) + (40125443/100000000000000 : ℝ)*(upper5) + (912676094216551/50000000000000 : ℝ)*(major0) + (912676094216551/50000000000000 : ℝ)*(major1) + (912676094216551/50000000000000 : ℝ)*(major2) + (675391677229609/25000000000000 : ℝ)*(sp0) + (2701574500546519/100000000000000 : ℝ)*(sp1) + (1350787643217341/50000000000000 : ℝ)*(sp2) + (237280538542491/25000000000000 : ℝ)*(sp3) + (9721643391/100000000000000 : ℝ)*(sp4) + (2666526907/50000000000000 : ℝ)*(sp7) + (474563743611889/50000000000000 : ℝ)*(f.failure) + (2701576430561827/100000000000000 : ℝ)*(f.sum) + (141981224233749/40955000000000000000000000000 : ℝ)*base65 + (10056672104752786297/2047750000000000000000000000000000 : ℝ)*base67 + (15084064095542286297/2047750000000000000000000000000000 : ℝ)*base69 + (10536673088241286297/2047750000000000000000000000000000 : ℝ)*base71 + (11740982143471/10238750000000000000000000000 : ℝ)*base73 + (5520337482499213703/2047750000000000000000000000000000 : ℝ)*base76 + (14686782368519536297/2047750000000000000000000000000000 : ℝ)*base77 + (30345541944586536297/2047750000000000000000000000000000 : ℝ)*base79 + (12185381655523/20477500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1873681/625000000000000000000 : ℝ)*base90 + (1873681/625000000000000000000 : ℝ)*base92 + (1873681/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10992040439689939458654213579/1023875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1573268603/100000000000000 : ℝ)*(base19) + (514994401/25000000000000 : ℝ)*(base23) + (52773313/25000000000000 : ℝ)*(upper3) + (70222587/50000000000000 : ℝ)*(lower4) + (5741099/3125000000000 : ℝ)*(upper5) + (1870729982668119/100000000000000 : ℝ)*(major0) + (1870729982668119/100000000000000 : ℝ)*(major1) + (1870729982668119/100000000000000 : ℝ)*(major2) + (5828176103/50000000000000 : ℝ)*(sp1) + (9110512077/50000000000000 : ℝ)*(sp2) + (1384368525358307/50000000000000 : ℝ)*(sp4) + (1384361910547903/50000000000000 : ℝ)*(sp5) + (346089596214357/12500000000000 : ℝ)*(sp6) + (486361278381059/50000000000000 : ℝ)*(sp7) + (486361278381059/50000000000000 : ℝ)*(f.failure) + (1384368525358307/50000000000000 : ℝ)*(f.sum) + (58439065095903/10238750000000000000000000000 : ℝ)*base66 + (24857696614307628807/4095500000000000000000000000000000 : ℝ)*base68 + (7189635338249371193/4095500000000000000000000000000000 : ℝ)*base69 + (46301590673864628807/4095500000000000000000000000000000 : ℝ)*base72 + (9692361234709/5119375000000000000000000000 : ℝ)*base74 + (51435043013149628807/4095500000000000000000000000000000 : ℝ)*base76 + (4526577148016628807/4095500000000000000000000000000000 : ℝ)*base78 + (2581034609836628807/4095500000000000000000000000000000 : ℝ)*base80 + (17594885480937/10238750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3453389/625000000000000000000 : ℝ)*base89 + (3453389/625000000000000000000 : ℝ)*base91 + (3453389/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1702_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1453/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1203/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8759/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1702_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1702_s2_0 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-180166111/1250000000 : ℝ)*x 0 + (5475911609/10000000000 : ℝ)*x 1 + (2568319087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180166111/1250000000 : ℝ)^5239 ≤ (450154321881/5000000000000 : ℝ)^4215 := by
    have hnat : (180166111 : ℕ)^5239*5000000000000^4215 ≤ 450154321881^4215*1250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180166111 1250000000 450154321881 5000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475911609/10000000000 : ℝ)^5239 ≤ (47306034474357/100000000000000 : ℝ)^4215 := by
    have hnat : (5475911609 : ℕ)^5239*100000000000000^4215 ≤ 47306034474357^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475911609 10000000000 47306034474357 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568319087/5000000000 : ℝ)^5239 ≤ (4369087907227/10000000000000 : ℝ)^4215 := by
    have hnat : (2568319087 : ℕ)^5239*10000000000000^4215 ≤ 4369087907227^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568319087 5000000000 4369087907227 10000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-180166111/1250000000 : ℝ), (5475911609/10000000000 : ℝ), (2568319087/5000000000 : ℝ)] ![(450154321881/5000000000000 : ℝ), (47306034474357/100000000000000 : ℝ), (4369087907227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-180166111/1250000000 : ℝ)|^5239 ≤ (450154321881/5000000000000 : ℝ)^4215
        have hw : |(-180166111/1250000000 : ℝ)|=(180166111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475911609/10000000000 : ℝ)|^5239 ≤ (47306034474357/100000000000000 : ℝ)^4215
        have hw : |(5475911609/10000000000 : ℝ)|=(5475911609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568319087/5000000000 : ℝ)|^5239 ≤ (4369087907227/10000000000000 : ℝ)^4215
        have hw : |(2568319087/5000000000 : ℝ)|=(2568319087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s2_1 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167074961/312500000 : ℝ)*x 0 + (-404348771/2500000000 : ℝ)*x 1 + (513663839/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167074961/312500000 : ℝ)^5239 ≤ (45919384759511/100000000000000 : ℝ)^4215 := by
    have hnat : (167074961 : ℕ)^5239*100000000000000^4215 ≤ 45919384759511^4215*312500000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167074961 312500000 45919384759511 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404348771/2500000000 : ℝ)^5239 ≤ (10389733879391/100000000000000 : ℝ)^4215 := by
    have hnat : (404348771 : ℕ)^5239*100000000000000^4215 ≤ 10389733879391^4215*2500000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404348771 2500000000 10389733879391 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513663839/1000000000 : ℝ)^5239 ≤ (43690881355851/100000000000000 : ℝ)^4215 := by
    have hnat : (513663839 : ℕ)^5239*100000000000000^4215 ≤ 43690881355851^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513663839 1000000000 43690881355851 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167074961/312500000 : ℝ), (-404348771/2500000000 : ℝ), (513663839/1000000000 : ℝ)] ![(45919384759511/100000000000000 : ℝ), (10389733879391/100000000000000 : ℝ), (43690881355851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167074961/312500000 : ℝ)|^5239 ≤ (45919384759511/100000000000000 : ℝ)^4215
        have hw : |(167074961/312500000 : ℝ)|=(167074961/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404348771/2500000000 : ℝ)|^5239 ≤ (10389733879391/100000000000000 : ℝ)^4215
        have hw : |(-404348771/2500000000 : ℝ)|=(404348771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513663839/1000000000 : ℝ)|^5239 ≤ (43690881355851/100000000000000 : ℝ)^4215
        have hw : |(513663839/1000000000 : ℝ)|=(513663839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s2_2 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346398551/10000000000 : ℝ)*x 0 + (5136638259/10000000000 : ℝ)*x 1 + (-808697763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346398551/10000000000 : ℝ)^5239 ≤ (45919382613749/100000000000000 : ℝ)^4215 := by
    have hnat : (5346398551 : ℕ)^5239*100000000000000^4215 ≤ 45919382613749^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346398551 10000000000 45919382613749 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136638259/10000000000 : ℝ)^5239 ≤ (21845439985451/50000000000000 : ℝ)^4215 := by
    have hnat : (5136638259 : ℕ)^5239*50000000000000^4215 ≤ 21845439985451^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136638259 10000000000 21845439985451 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808697763/5000000000 : ℝ)^5239 ≤ (10389737408471/100000000000000 : ℝ)^4215 := by
    have hnat : (808697763 : ℕ)^5239*100000000000000^4215 ≤ 10389737408471^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808697763 5000000000 10389737408471 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346398551/10000000000 : ℝ), (5136638259/10000000000 : ℝ), (-808697763/5000000000 : ℝ)] ![(45919382613749/100000000000000 : ℝ), (21845439985451/50000000000000 : ℝ), (10389737408471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346398551/10000000000 : ℝ)|^5239 ≤ (45919382613749/100000000000000 : ℝ)^4215
        have hw : |(5346398551/10000000000 : ℝ)|=(5346398551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136638259/10000000000 : ℝ)|^5239 ≤ (21845439985451/50000000000000 : ℝ)^4215
        have hw : |(5136638259/10000000000 : ℝ)|=(5136638259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-808697763/5000000000 : ℝ)|^5239 ≤ (10389737408471/100000000000000 : ℝ)^4215
        have hw : |(-808697763/5000000000 : ℝ)|=(808697763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s2_3 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2057492351/5000000000 : ℝ)*x 0 + (91260893/250000000 : ℝ)*x 1 + (461613749/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057492351/5000000000 : ℝ)^5239 ≤ (3316516167923/10000000000000 : ℝ)^4215 := by
    have hnat : (2057492351 : ℕ)^5239*10000000000000^4215 ≤ 3316516167923^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057492351 5000000000 3316516167923 10000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91260893/250000000 : ℝ)^5239 ≤ (3572151921347/12500000000000 : ℝ)^4215 := by
    have hnat : (91260893 : ℕ)^5239*12500000000000^4215 ≤ 3572151921347^4215*250000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91260893 250000000 3572151921347 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461613749/1000000000 : ℝ)^5239 ≤ (3825762293423/10000000000000 : ℝ)^4215 := by
    have hnat : (461613749 : ℕ)^5239*10000000000000^4215 ≤ 3825762293423^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461613749 1000000000 3825762293423 10000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2057492351/5000000000 : ℝ), (91260893/250000000 : ℝ), (461613749/1000000000 : ℝ)] ![(3316516167923/10000000000000 : ℝ), (3572151921347/12500000000000 : ℝ), (3825762293423/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2057492351/5000000000 : ℝ)|^5239 ≤ (3316516167923/10000000000000 : ℝ)^4215
        have hw : |(2057492351/5000000000 : ℝ)|=(2057492351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91260893/250000000 : ℝ)|^5239 ≤ (3572151921347/12500000000000 : ℝ)^4215
        have hw : |(91260893/250000000 : ℝ)|=(91260893/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461613749/1000000000 : ℝ)|^5239 ≤ (3825762293423/10000000000000 : ℝ)^4215
        have hw : |(461613749/1000000000 : ℝ)|=(461613749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s2_4 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-720742583/5000000000 : ℝ)*x 0 + (1028076699/2000000000 : ℝ)*x 1 + (547211039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (720742583/5000000000 : ℝ)^5239 ≤ (2251074944543/25000000000000 : ℝ)^4215 := by
    have hnat : (720742583 : ℕ)^5239*25000000000000^4215 ≤ 2251074944543^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720742583 5000000000 2251074944543 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028076699/2000000000 : ℝ)^5239 ≤ (5466309826401/12500000000000 : ℝ)^4215 := by
    have hnat : (1028076699 : ℕ)^5239*12500000000000^4215 ≤ 5466309826401^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028076699 2000000000 5466309826401 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547211039/1000000000 : ℝ)^5239 ≤ (47265221598591/100000000000000 : ℝ)^4215 := by
    have hnat : (547211039 : ℕ)^5239*100000000000000^4215 ≤ 47265221598591^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547211039 1000000000 47265221598591 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-720742583/5000000000 : ℝ), (1028076699/2000000000 : ℝ), (547211039/1000000000 : ℝ)] ![(2251074944543/25000000000000 : ℝ), (5466309826401/12500000000000 : ℝ), (47265221598591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-720742583/5000000000 : ℝ)|^5239 ≤ (2251074944543/25000000000000 : ℝ)^4215
        have hw : |(-720742583/5000000000 : ℝ)|=(720742583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028076699/2000000000 : ℝ)|^5239 ≤ (5466309826401/12500000000000 : ℝ)^4215
        have hw : |(1028076699/2000000000 : ℝ)|=(1028076699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547211039/1000000000 : ℝ)|^5239 ≤ (47265221598591/100000000000000 : ℝ)^4215
        have hw : |(547211039/1000000000 : ℝ)|=(547211039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s2_5 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82118909/156250000 : ℝ)*x 0 + (-1281923201/10000000000 : ℝ)*x 1 + (5472110389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82118909/156250000 : ℝ)^5239 ≤ (1798087406691/4000000000000 : ℝ)^4215 := by
    have hnat : (82118909 : ℕ)^5239*4000000000000^4215 ≤ 1798087406691^4215*156250000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82118909 156250000 1798087406691 4000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281923201/10000000000 : ℝ)^5239 ≤ (972824153427/12500000000000 : ℝ)^4215 := by
    have hnat : (1281923201 : ℕ)^5239*12500000000000^4215 ≤ 972824153427^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281923201 10000000000 972824153427 12500000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472110389/10000000000 : ℝ)^5239 ≤ (9453044317571/20000000000000 : ℝ)^4215 := by
    have hnat : (5472110389 : ℕ)^5239*20000000000000^4215 ≤ 9453044317571^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472110389 10000000000 9453044317571 20000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82118909/156250000 : ℝ), (-1281923201/10000000000 : ℝ), (5472110389/10000000000 : ℝ)] ![(1798087406691/4000000000000 : ℝ), (972824153427/12500000000000 : ℝ), (9453044317571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82118909/156250000 : ℝ)|^5239 ≤ (1798087406691/4000000000000 : ℝ)^4215
        have hw : |(82118909/156250000 : ℝ)|=(82118909/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1281923201/10000000000 : ℝ)|^5239 ≤ (972824153427/12500000000000 : ℝ)^4215
        have hw : |(-1281923201/10000000000 : ℝ)|=(1281923201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472110389/10000000000 : ℝ)|^5239 ≤ (9453044317571/20000000000000 : ℝ)^4215
        have hw : |(5472110389/10000000000 : ℝ)|=(5472110389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s2_6 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210224407/400000000 : ℝ)*x 0 + (547211039/1000000000 : ℝ)*x 1 + (-640961601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210224407/400000000 : ℝ)^5239 ≤ (44952185156643/100000000000000 : ℝ)^4215 := by
    have hnat : (210224407 : ℕ)^5239*100000000000000^4215 ≤ 44952185156643^4215*400000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210224407 400000000 44952185156643 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547211039/1000000000 : ℝ)^5239 ≤ (47265221598591/100000000000000 : ℝ)^4215 := by
    have hnat : (547211039 : ℕ)^5239*100000000000000^4215 ≤ 47265221598591^4215*1000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547211039 1000000000 47265221598591 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640961601/5000000000 : ℝ)^5239 ≤ (3891296617481/50000000000000 : ℝ)^4215 := by
    have hnat : (640961601 : ℕ)^5239*50000000000000^4215 ≤ 3891296617481^4215*5000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640961601 5000000000 3891296617481 50000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210224407/400000000 : ℝ), (547211039/1000000000 : ℝ), (-640961601/5000000000 : ℝ)] ![(44952185156643/100000000000000 : ℝ), (47265221598591/100000000000000 : ℝ), (3891296617481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210224407/400000000 : ℝ)|^5239 ≤ (44952185156643/100000000000000 : ℝ)^4215
        have hw : |(210224407/400000000 : ℝ)|=(210224407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547211039/1000000000 : ℝ)|^5239 ≤ (47265221598591/100000000000000 : ℝ)^4215
        have hw : |(547211039/1000000000 : ℝ)|=(547211039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-640961601/5000000000 : ℝ)|^5239 ≤ (3891296617481/50000000000000 : ℝ)^4215
        have hw : |(-640961601/5000000000 : ℝ)|=(640961601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1702_s2_7 (p : ℝ) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823086029/2000000000 : ℝ)*x 0 + (4605476837/10000000000 : ℝ)*x 1 + (3661256259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823086029/2000000000 : ℝ)^5239 ≤ (33169624018251/100000000000000 : ℝ)^4215 := by
    have hnat : (823086029 : ℕ)^5239*100000000000000^4215 ≤ 33169624018251^4215*2000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823086029 2000000000 33169624018251 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4605476837/10000000000 : ℝ)^5239 ≤ (9536958918109/25000000000000 : ℝ)^4215 := by
    have hnat : (4605476837 : ℕ)^5239*25000000000000^4215 ≤ 9536958918109^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4605476837 10000000000 9536958918109 25000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3661256259/10000000000 : ℝ)^5239 ≤ (28682540292341/100000000000000 : ℝ)^4215 := by
    have hnat : (3661256259 : ℕ)^5239*100000000000000^4215 ≤ 28682540292341^4215*10000000000^5239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661256259 10000000000 28682540292341 100000000000000 5239 4215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5239/1024 : ℝ)) 5239 4215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823086029/2000000000 : ℝ), (4605476837/10000000000 : ℝ), (3661256259/10000000000 : ℝ)] ![(33169624018251/100000000000000 : ℝ), (9536958918109/25000000000000 : ℝ), (28682540292341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823086029/2000000000 : ℝ)|^5239 ≤ (33169624018251/100000000000000 : ℝ)^4215
        have hw : |(823086029/2000000000 : ℝ)|=(823086029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4605476837/10000000000 : ℝ)|^5239 ≤ (9536958918109/25000000000000 : ℝ)^4215
        have hw : |(4605476837/10000000000 : ℝ)|=(4605476837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3661256259/10000000000 : ℝ)|^5239 ≤ (28682540292341/100000000000000 : ℝ)^4215
        have hw : |(3661256259/10000000000 : ℝ)|=(3661256259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1702_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8759/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1203/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (993/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3433/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8759/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1203/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8759/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1203/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8759/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1203/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8759/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1203/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8759/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1203/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8759/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1203/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1203/12500 : ℝ) ^ (5231/1024 : ℝ) ≤ (640582999597089/100000000000000000000 : ℝ) := by
    have hpowers : (1203/12500 : ℝ)^5231 ≤ (640582999597089/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1203 : ℕ)^5231*100000000000000000000^1024 ≤ 640582999597089^1024*12500^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1203 12500 640582999597089 100000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1203/12500 : ℝ)) (X := (640582999597089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8759/50000 : ℝ) ^ (5231/1024 : ℝ) ≤ (3414739064858169/25000000000000000000 : ℝ) := by
    have hpowers : (8759/50000 : ℝ)^5231 ≤ (3414739064858169/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8759 : ℕ)^5231*25000000000000000000^1024 ≤ 3414739064858169^1024*50000^5231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8759 50000 3414739064858169 25000000000000000000 5231 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8759/50000 : ℝ)) (X := (3414739064858169/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000640582999597089/50000000000000000000 : ℝ) ≤ (2500006269868211/2500000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (50000640582999597089/50000000000000000000 : ℝ)^1024 ≤ (2500006269868211/2500000000000000 : ℝ)^5231 := by
      have hnat : (50000640582999597089 : ℕ)^1024*2500000000000000^5231 ≤ 2500006269868211^5231*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000640582999597089 50000000000000000000 2500006269868211 2500000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500006269868211/2500000000000000 : ℝ)) (X := (50000640582999597089/50000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002859907851805953/20000000000000000000 : ℝ) ≤ (5000139953032819/5000000000000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (20002859907851805953/20000000000000000000 : ℝ)^1024 ≤ (5000139953032819/5000000000000000 : ℝ)^5231 := by
      have hnat : (20002859907851805953 : ℕ)^1024*5000000000000000^5231 ≤ 5000139953032819^5231*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002859907851805953 20000000000000000000 5000139953032819 5000000000000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139953032819/5000000000000000 : ℝ)) (X := (20002859907851805953/20000000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503414739064858169/12500000000000000000 : ℝ) ≤ (39064588799447/39062500000000 : ℝ) ^ (5231/1024 : ℝ) := by
    have hpowers : (12503414739064858169/12500000000000000000 : ℝ)^1024 ≤ (39064588799447/39062500000000 : ℝ)^5231 := by
      have hnat : (12503414739064858169 : ℕ)^1024*39062500000000^5231 ≤ 39064588799447^5231*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503414739064858169 12500000000000000000 39064588799447 39062500000000 1024 5231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39064588799447/39062500000000 : ℝ)) (X := (12503414739064858169/12500000000000000000 : ℝ)) (by norm_num) 5231 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(640582999597089/100000000000000000000 : ℝ) ≤ ((9866911634387566453/9867500000000000000 : ℝ)+2*(127413296397/394700000000000 : ℝ)*(1203/12500 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (9866911634387566453/9867500000000000000 : ℝ)+2*(127413296397/394700000000000 : ℝ)*(1203/12500 : ℝ)=(2500006269868211/2500000000000000 : ℝ) by norm_num, show 1+2*(640582999597089/100000000000000000000 : ℝ)=(50000640582999597089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3414739064858169/25000000000000000000 : ℝ)+(640582999597089/100000000000000000000 : ℝ) ≤ ((9866911634387566453/9867500000000000000 : ℝ)+(127413296397/394700000000000 : ℝ)*((8759/50000 : ℝ)+(1203/12500 : ℝ)))^(5231/1024 : ℝ) := by
    rw [show (9866911634387566453/9867500000000000000 : ℝ)+(127413296397/394700000000000 : ℝ)*((8759/50000 : ℝ)+(1203/12500 : ℝ))=(5000139953032819/5000000000000000 : ℝ) by norm_num, show 1+(3414739064858169/25000000000000000000 : ℝ)+(640582999597089/100000000000000000000 : ℝ)=(20002859907851805953/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3414739064858169/25000000000000000000 : ℝ) ≤ ((9866911634387566453/9867500000000000000 : ℝ)+2*(127413296397/394700000000000 : ℝ)*(8759/50000 : ℝ))^(5231/1024 : ℝ) := by
    rw [show (9866911634387566453/9867500000000000000 : ℝ)+2*(127413296397/394700000000000 : ℝ)*(8759/50000 : ℝ)=(39064588799447/39062500000000 : ℝ) by norm_num, show 1+2*(3414739064858169/25000000000000000000 : ℝ)=(12503414739064858169/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9866911634387566453/9867500000000000000 : ℝ)*(X 1 0+X 2 0)+(127413296397/394700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1203/12500 : ℝ)) (hi := (8759/50000 : ℝ)) (c := (9866911634387566453/9867500000000000000 : ℝ)) (alpha := (127413296397/394700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9866911634387566453/9867500000000000000 : ℝ)*(X 0 1+X 2 1)+(127413296397/394700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1203/12500 : ℝ)) (hi := (8759/50000 : ℝ)) (c := (9866911634387566453/9867500000000000000 : ℝ)) (alpha := (127413296397/394700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9866911634387566453/9867500000000000000 : ℝ)*(X 0 2+X 1 2)+(127413296397/394700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5231/1024 : ℝ)) (lo := (1203/12500 : ℝ)) (hi := (8759/50000 : ℝ)) (c := (9866911634387566453/9867500000000000000 : ℝ)) (alpha := (127413296397/394700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-180166111/1250000000 : ℝ)*X 0 0+(5475911609/10000000000 : ℝ)*X 0 1+(2568319087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167074961/312500000 : ℝ)*X 1 0+(-404348771/2500000000 : ℝ)*X 1 1+(513663839/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346398551/10000000000 : ℝ)*X 2 0+(5136638259/10000000000 : ℝ)*X 2 1+(-808697763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2057492351/5000000000 : ℝ)*X 0 0+(91260893/250000000 : ℝ)*X 0 1+(461613749/1000000000 : ℝ)*X 0 2+(2057492351/5000000000 : ℝ)*X 1 0+(91260893/250000000 : ℝ)*X 1 1+(461613749/1000000000 : ℝ)*X 1 2+(2057492351/5000000000 : ℝ)*X 2 0+(91260893/250000000 : ℝ)*X 2 1+(461613749/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-720742583/5000000000 : ℝ)*X 0 0+(1028076699/2000000000 : ℝ)*X 0 1+(547211039/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82118909/156250000 : ℝ)*X 1 0+(-1281923201/10000000000 : ℝ)*X 1 1+(5472110389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((210224407/400000000 : ℝ)*X 2 0+(547211039/1000000000 : ℝ)*X 2 1+(-640961601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((823086029/2000000000 : ℝ)*X 0 0+(4605476837/10000000000 : ℝ)*X 0 1+(3661256259/10000000000 : ℝ)*X 0 2+(823086029/2000000000 : ℝ)*X 1 0+(4605476837/10000000000 : ℝ)*X 1 1+(3661256259/10000000000 : ℝ)*X 1 2+(823086029/2000000000 : ℝ)*X 2 0+(4605476837/10000000000 : ℝ)*X 2 1+(3661256259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1702_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1236314729401235322592896873/98675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2044004611/100000000000000 : ℝ)*(base19) + (1927550541/100000000000000 : ℝ)*(base23) + (29111641/6250000000000 : ℝ)*(upper3) + (3015959/100000000000000 : ℝ)*(upper4) + (85081931/50000000000000 : ℝ)*(upper5) + (398304810778047/20000000000000 : ℝ)*(major0) + (398304810778047/20000000000000 : ℝ)*(major1) + (398304810778047/20000000000000 : ℝ)*(major2) + (1473749126848343/50000000000000 : ℝ)*(sp0) + (1473756927535567/50000000000000 : ℝ)*(sp1) + (2947513971525203/100000000000000 : ℝ)*(sp2) + (64720201952789/6250000000000 : ℝ)*(sp3) + (17645379059/100000000000000 : ℝ)*(sp4) + (4279910737/50000000000000 : ℝ)*(sp7) + (517765895533049/50000000000000 : ℝ)*(f.failure) + (92109871846117/3125000000000 : ℝ)*(f.sum) + (18206930461093/3947000000000000000000000000 : ℝ)*base66 + (238305443745417709/197350000000000000000000000000000 : ℝ)*base68 + (549427362597532291/197350000000000000000000000000000 : ℝ)*base69 + (1865076205990567709/197350000000000000000000000000000 : ℝ)*base72 + (710268284409/789400000000000000000000000 : ℝ)*base73 + (2394643861904567709/197350000000000000000000000000000 : ℝ)*base76 + (67287979365317709/197350000000000000000000000000000 : ℝ)*base78 + (476479955539282291/197350000000000000000000000000000 : ℝ)*base79 + (8223973745303/3947000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5446679/625000000000000000000 : ℝ)*base89 + (5446679/625000000000000000000 : ℝ)*base91 + (5446679/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (589526497507428549475480209/61671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1336977737/100000000000000 : ℝ)*(base19) + (180001293/12500000000000 : ℝ)*(base23) + (8182259/4000000000000 : ℝ)*(upper3) + (9293839/20000000000000 : ℝ)*(lower4) + (390989/195312500000 : ℝ)*(upper5) + (63650032160153/3125000000000 : ℝ)*(major0) + (63650032160153/3125000000000 : ℝ)*(major1) + (63650032160153/3125000000000 : ℝ)*(major2) + (11938726141/100000000000000 : ℝ)*(sp1) + (12817959711/100000000000000 : ℝ)*(sp2) + (1507263650907869/50000000000000 : ℝ)*(sp4) + (3014514026111861/100000000000000 : ℝ)*(sp5) + (3014513043845683/100000000000000 : ℝ)*(sp6) + (105907443779799/10000000000000 : ℝ)*(sp7) + (105907443779799/10000000000000 : ℝ)*(f.failure) + (1507263650907869/50000000000000 : ℝ)*(f.sum) + (24802443230421/9867500000000000000000000000 : ℝ)*base65 + (129968782197953559/30835937500000000000000000000000 : ℝ)*base67 + (15495853531107449/1927246093750000000000000000000 : ℝ)*base69 + (16358214958539171/7708984375000000000000000000000 : ℝ)*base71 + (13229064426837/19735000000000000000000000000 : ℝ)*base73 + (98406519250702257/61671875000000000000000000000000 : ℝ)*base76 + (26168544233016059/30835937500000000000000000000000 : ℝ)*base77 + (371089696897110243/61671875000000000000000000000000 : ℝ)*base79 + (30464775723041/9867500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (365929/125000000000000000000 : ℝ)*base89 + (365929/125000000000000000000 : ℝ)*base91 + (365929/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1702_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8759/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1203/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (993/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1702_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1702_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (993/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1702_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1702_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1702_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5231/1024 : ℝ) ≤ p) (hpb : p ≤ (5239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24039871/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (993/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3433/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1702_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
