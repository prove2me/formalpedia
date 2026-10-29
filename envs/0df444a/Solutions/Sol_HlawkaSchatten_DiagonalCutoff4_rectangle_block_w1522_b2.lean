-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1522_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:50.230545+00:00
-- url     : https://prove2.me/submissions/66cb17ee-e1cc-4fb3-9998-861aeaaf2b45

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
theorem support_rectangle_w1522_s6_0 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-926672653/5000000000 : ℝ)*x 0 + (5431935967/10000000000 : ℝ)*x 1 + (5218124999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926672653/5000000000 : ℝ)^4541 ≤ (11345314367251/100000000000000 : ℝ)^3517 := by
    have hnat : (926672653 : ℕ)^4541*100000000000000^3517 ≤ 11345314367251^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926672653 5000000000 11345314367251 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431935967/10000000000 : ℝ)^4541 ≤ (22738131410117/50000000000000 : ℝ)^3517 := by
    have hnat : (5431935967 : ℕ)^4541*50000000000000^3517 ≤ 22738131410117^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431935967 10000000000 22738131410117 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218124999/10000000000 : ℝ)^4541 ≤ (43178422793699/100000000000000 : ℝ)^3517 := by
    have hnat : (5218124999 : ℕ)^4541*100000000000000^3517 ≤ 43178422793699^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218124999 10000000000 43178422793699 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-926672653/5000000000 : ℝ), (5431935967/10000000000 : ℝ), (5218124999/10000000000 : ℝ)] ![(11345314367251/100000000000000 : ℝ), (22738131410117/50000000000000 : ℝ), (43178422793699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-926672653/5000000000 : ℝ)|^4541 ≤ (11345314367251/100000000000000 : ℝ)^3517
        have hw : |(-926672653/5000000000 : ℝ)|=(926672653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431935967/10000000000 : ℝ)|^4541 ≤ (22738131410117/50000000000000 : ℝ)^3517
        have hw : |(5431935967/10000000000 : ℝ)|=(5431935967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218124999/10000000000 : ℝ)|^4541 ≤ (43178422793699/100000000000000 : ℝ)^3517
        have hw : |(5218124999/10000000000 : ℝ)|=(5218124999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s6_1 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337757227/2500000000 : ℝ)*x 0 + (-1962826937/10000000000 : ℝ)*x 1 + (1043625023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337757227/2500000000 : ℝ)^4541 ≤ (8920718740721/20000000000000 : ℝ)^3517 := by
    have hnat : (1337757227 : ℕ)^4541*20000000000000^3517 ≤ 8920718740721^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337757227 2500000000 8920718740721 20000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1962826937/10000000000 : ℝ)^4541 ≤ (6108991120743/50000000000000 : ℝ)^3517 := by
    have hnat : (1962826937 : ℕ)^4541*50000000000000^3517 ≤ 6108991120743^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962826937 10000000000 6108991120743 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043625023/2000000000 : ℝ)^4541 ≤ (10794606008259/25000000000000 : ℝ)^3517 := by
    have hnat : (1043625023 : ℕ)^4541*25000000000000^3517 ≤ 10794606008259^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043625023 2000000000 10794606008259 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337757227/2500000000 : ℝ), (-1962826937/10000000000 : ℝ), (1043625023/2000000000 : ℝ)] ![(8920718740721/20000000000000 : ℝ), (6108991120743/50000000000000 : ℝ), (10794606008259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337757227/2500000000 : ℝ)|^4541 ≤ (8920718740721/20000000000000 : ℝ)^3517
        have hw : |(1337757227/2500000000 : ℝ)|=(1337757227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1962826937/10000000000 : ℝ)|^4541 ≤ (6108991120743/50000000000000 : ℝ)^3517
        have hw : |(-1962826937/10000000000 : ℝ)|=(1962826937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043625023/2000000000 : ℝ)|^4541 ≤ (10794606008259/25000000000000 : ℝ)^3517
        have hw : |(1043625023/2000000000 : ℝ)|=(1043625023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s6_2 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675514469/5000000000 : ℝ)*x 0 + (1043625007/2000000000 : ℝ)*x 1 + (-490706751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675514469/5000000000 : ℝ)^4541 ≤ (44603594026479/100000000000000 : ℝ)^3517 := by
    have hnat : (2675514469 : ℕ)^4541*100000000000000^3517 ≤ 44603594026479^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675514469 5000000000 44603594026479 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043625007/2000000000 : ℝ)^4541 ≤ (43178423178321/100000000000000 : ℝ)^3517 := by
    have hnat : (1043625007 : ℕ)^4541*100000000000000^3517 ≤ 43178423178321^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043625007 2000000000 43178423178321 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490706751/2500000000 : ℝ)^4541 ≤ (190905980937/1562500000000 : ℝ)^3517 := by
    have hnat : (490706751 : ℕ)^4541*1562500000000^3517 ≤ 190905980937^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490706751 2500000000 190905980937 1562500000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675514469/5000000000 : ℝ), (1043625007/2000000000 : ℝ), (-490706751/2500000000 : ℝ)] ![(44603594026479/100000000000000 : ℝ), (43178423178321/100000000000000 : ℝ), (190905980937/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675514469/5000000000 : ℝ)|^4541 ≤ (44603594026479/100000000000000 : ℝ)^3517
        have hw : |(2675514469/5000000000 : ℝ)|=(2675514469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043625007/2000000000 : ℝ)|^4541 ≤ (43178423178321/100000000000000 : ℝ)^3517
        have hw : |(1043625007/2000000000 : ℝ)|=(1043625007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490706751/2500000000 : ℝ)|^4541 ≤ (190905980937/1562500000000 : ℝ)^3517
        have hw : |(-490706751/2500000000 : ℝ)|=(490706751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s6_3 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066284471/2500000000 : ℝ)*x 0 + (1006723523/2500000000 : ℝ)*x 1 + (56439339/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066284471/2500000000 : ℝ)^4541 ≤ (33280160549431/100000000000000 : ℝ)^3517 := by
    have hnat : (1066284471 : ℕ)^4541*100000000000000^3517 ≤ 33280160549431^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066284471 2500000000 33280160549431 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006723523/2500000000 : ℝ)^4541 ≤ (3862463942749/12500000000000 : ℝ)^3517 := by
    have hnat : (1006723523 : ℕ)^4541*12500000000000^3517 ≤ 3862463942749^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006723523 2500000000 3862463942749 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56439339/125000000 : ℝ)^4541 ≤ (35820127903613/100000000000000 : ℝ)^3517 := by
    have hnat : (56439339 : ℕ)^4541*100000000000000^3517 ≤ 35820127903613^3517*125000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56439339 125000000 35820127903613 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066284471/2500000000 : ℝ), (1006723523/2500000000 : ℝ), (56439339/125000000 : ℝ)] ![(33280160549431/100000000000000 : ℝ), (3862463942749/12500000000000 : ℝ), (35820127903613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066284471/2500000000 : ℝ)|^4541 ≤ (33280160549431/100000000000000 : ℝ)^3517
        have hw : |(1066284471/2500000000 : ℝ)|=(1066284471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006723523/2500000000 : ℝ)|^4541 ≤ (3862463942749/12500000000000 : ℝ)^3517
        have hw : |(1006723523/2500000000 : ℝ)|=(1006723523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56439339/125000000 : ℝ)|^4541 ≤ (35820127903613/100000000000000 : ℝ)^3517
        have hw : |(56439339/125000000 : ℝ)|=(56439339/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s6_4 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-926686689/5000000000 : ℝ)*x 0 + (208769121/400000000 : ℝ)*x 1 + (5430825171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926686689/5000000000 : ℝ)^4541 ≤ (5672768122471/50000000000000 : ℝ)^3517 := by
    have hnat : (926686689 : ℕ)^4541*50000000000000^3517 ≤ 5672768122471^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926686689 5000000000 5672768122471 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208769121/400000000 : ℝ)^4541 ≤ (10797551954911/25000000000000 : ℝ)^3517 := by
    have hnat : (208769121 : ℕ)^4541*25000000000000^3517 ≤ 10797551954911^3517*400000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208769121 400000000 10797551954911 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430825171/10000000000 : ℝ)^4541 ≤ (45464255927327/100000000000000 : ℝ)^3517 := by
    have hnat : (5430825171 : ℕ)^4541*100000000000000^3517 ≤ 45464255927327^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430825171 10000000000 45464255927327 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-926686689/5000000000 : ℝ), (208769121/400000000 : ℝ), (5430825171/10000000000 : ℝ)] ![(5672768122471/50000000000000 : ℝ), (10797551954911/25000000000000 : ℝ), (45464255927327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-926686689/5000000000 : ℝ)|^4541 ≤ (5672768122471/50000000000000 : ℝ)^3517
        have hw : |(-926686689/5000000000 : ℝ)|=(926686689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208769121/400000000 : ℝ)|^4541 ≤ (10797551954911/25000000000000 : ℝ)^3517
        have hw : |(208769121/400000000 : ℝ)|=(208769121/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430825171/10000000000 : ℝ)|^4541 ≤ (45464255927327/100000000000000 : ℝ)^3517
        have hw : |(5430825171/10000000000 : ℝ)|=(5430825171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s6_5 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294817827/10000000000 : ℝ)*x 0 + (-1750126889/10000000000 : ℝ)*x 1 + (5430825047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294817827/10000000000 : ℝ)^4541 ≤ (10999887866557/25000000000000 : ℝ)^3517 := by
    have hnat : (5294817827 : ℕ)^4541*25000000000000^3517 ≤ 10999887866557^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294817827 10000000000 10999887866557 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1750126889/10000000000 : ℝ)^4541 ≤ (2634048483273/25000000000000 : ℝ)^3517 := by
    have hnat : (1750126889 : ℕ)^4541*25000000000000^3517 ≤ 2634048483273^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750126889 10000000000 2634048483273 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430825047/10000000000 : ℝ)^4541 ≤ (45464254587017/100000000000000 : ℝ)^3517 := by
    have hnat : (5430825047 : ℕ)^4541*100000000000000^3517 ≤ 45464254587017^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430825047 10000000000 45464254587017 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294817827/10000000000 : ℝ), (-1750126889/10000000000 : ℝ), (5430825047/10000000000 : ℝ)] ![(10999887866557/25000000000000 : ℝ), (2634048483273/25000000000000 : ℝ), (45464254587017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294817827/10000000000 : ℝ)|^4541 ≤ (10999887866557/25000000000000 : ℝ)^3517
        have hw : |(5294817827/10000000000 : ℝ)|=(5294817827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1750126889/10000000000 : ℝ)|^4541 ≤ (2634048483273/25000000000000 : ℝ)^3517
        have hw : |(-1750126889/10000000000 : ℝ)|=(1750126889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430825047/10000000000 : ℝ)|^4541 ≤ (45464254587017/100000000000000 : ℝ)^3517
        have hw : |(5430825047/10000000000 : ℝ)|=(5430825047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s6_6 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294817481/10000000000 : ℝ)*x 0 + (678853143/1250000000 : ℝ)*x 1 + (-1750127231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294817481/10000000000 : ℝ)^4541 ≤ (5499943469231/12500000000000 : ℝ)^3517 := by
    have hnat : (5294817481 : ℕ)^4541*12500000000000^3517 ≤ 5499943469231^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294817481 10000000000 5499943469231 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678853143/1250000000 : ℝ)^4541 ≤ (9092851127097/20000000000000 : ℝ)^3517 := by
    have hnat : (678853143 : ℕ)^4541*20000000000000^3517 ≤ 9092851127097^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678853143 1250000000 9092851127097 20000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1750127231/10000000000 : ℝ)^4541 ≤ (10536196591487/100000000000000 : ℝ)^3517 := by
    have hnat : (1750127231 : ℕ)^4541*100000000000000^3517 ≤ 10536196591487^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750127231 10000000000 10536196591487 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294817481/10000000000 : ℝ), (678853143/1250000000 : ℝ), (-1750127231/10000000000 : ℝ)] ![(5499943469231/12500000000000 : ℝ), (9092851127097/20000000000000 : ℝ), (10536196591487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294817481/10000000000 : ℝ)|^4541 ≤ (5499943469231/12500000000000 : ℝ)^3517
        have hw : |(5294817481/10000000000 : ℝ)|=(5294817481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678853143/1250000000 : ℝ)|^4541 ≤ (9092851127097/20000000000000 : ℝ)^3517
        have hw : |(678853143/1250000000 : ℝ)|=(678853143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1750127231/10000000000 : ℝ)|^4541 ≤ (10536196591487/100000000000000 : ℝ)^3517
        have hw : |(-1750127231/10000000000 : ℝ)|=(1750127231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s6_7 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4265200869/10000000000 : ℝ)*x 0 + (2256315141/5000000000 : ℝ)*x 1 + (4029431713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265200869/10000000000 : ℝ)^4541 ≤ (16640397552411/50000000000000 : ℝ)^3517 := by
    have hnat : (4265200869 : ℕ)^4541*50000000000000^3517 ≤ 16640397552411^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265200869 10000000000 16640397552411 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256315141/5000000000 : ℝ)^4541 ≤ (35794349597649/100000000000000 : ℝ)^3517 := by
    have hnat : (2256315141 : ℕ)^4541*100000000000000^3517 ≤ 35794349597649^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256315141 5000000000 35794349597649 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029431713/10000000000 : ℝ)^4541 ≤ (30924855285899/100000000000000 : ℝ)^3517 := by
    have hnat : (4029431713 : ℕ)^4541*100000000000000^3517 ≤ 30924855285899^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029431713 10000000000 30924855285899 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265200869/10000000000 : ℝ), (2256315141/5000000000 : ℝ), (4029431713/10000000000 : ℝ)] ![(16640397552411/50000000000000 : ℝ), (35794349597649/100000000000000 : ℝ), (30924855285899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265200869/10000000000 : ℝ)|^4541 ≤ (16640397552411/50000000000000 : ℝ)^3517
        have hw : |(4265200869/10000000000 : ℝ)|=(4265200869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256315141/5000000000 : ℝ)|^4541 ≤ (35794349597649/100000000000000 : ℝ)^3517
        have hw : |(2256315141/5000000000 : ℝ)|=(2256315141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029431713/10000000000 : ℝ)|^4541 ≤ (30924855285899/100000000000000 : ℝ)^3517
        have hw : |(4029431713/10000000000 : ℝ)|=(4029431713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1522_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10953/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5477/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10953/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10953/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10953/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10953/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10953/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10953/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10953/100000 : ℝ) ^ (4539/1024 : ℝ) ≤ (2764317102672239/50000000000000000000 : ℝ) := by
    have hpowers : (10953/100000 : ℝ)^4539 ≤ (2764317102672239/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10953 : ℕ)^4539*50000000000000000000^1024 ≤ 2764317102672239^1024*100000^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10953 100000 2764317102672239 50000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10953/100000 : ℝ)) (X := (2764317102672239/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4539/1024 : ℝ) ≤ (25648512490651323/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4539 ≤ (25648512490651323/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4539*100000000000000000000^1024 ≤ 25648512490651323^1024*25000^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 25648512490651323 100000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (25648512490651323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002764317102672239/25000000000000000000 : ℝ) ≤ (10000249441685829/10000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (25002764317102672239/25000000000000000000 : ℝ)^1024 ≤ (10000249441685829/10000000000000000 : ℝ)^4539 := by
      have hnat : (25002764317102672239 : ℕ)^1024*10000000000000000^4539 ≤ 10000249441685829^4539*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002764317102672239 25000000000000000000 10000249441685829 10000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000249441685829/10000000000000000 : ℝ)) (X := (25002764317102672239/25000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031177146695995801/100000000000000000000 : ℝ) ≤ (10000703272636299/10000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (100031177146695995801/100000000000000000000 : ℝ)^1024 ≤ (10000703272636299/10000000000000000 : ℝ)^4539 := by
      have hnat : (100031177146695995801 : ℕ)^1024*10000000000000000^4539 ≤ 10000703272636299^4539*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031177146695995801 100000000000000000000 10000703272636299 10000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000703272636299/10000000000000000 : ℝ)) (X := (100031177146695995801/100000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025648512490651323/50000000000000000000 : ℝ) ≤ (10001157103586769/10000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (50025648512490651323/50000000000000000000 : ℝ)^1024 ≤ (10001157103586769/10000000000000000 : ℝ)^4539 := by
      have hnat : (50025648512490651323 : ℕ)^1024*10000000000000000^4539 ≤ 10001157103586769^4539*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025648512490651323 50000000000000000000 10001157103586769 10000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001157103586769/10000000000000000 : ℝ)) (X := (50025648512490651323/50000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2764317102672239/50000000000000000000 : ℝ) ≤ ((45301188599477495379/45310000000000000000 : ℝ)+2*(45383095047/45310000000000 : ℝ)*(10953/100000 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (45301188599477495379/45310000000000000000 : ℝ)+2*(45383095047/45310000000000 : ℝ)*(10953/100000 : ℝ)=(10000249441685829/10000000000000000 : ℝ) by norm_num, show 1+2*(2764317102672239/50000000000000000000 : ℝ)=(25002764317102672239/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25648512490651323/100000000000000000000 : ℝ)+(2764317102672239/50000000000000000000 : ℝ) ≤ ((45301188599477495379/45310000000000000000 : ℝ)+(45383095047/45310000000000 : ℝ)*((3871/25000 : ℝ)+(10953/100000 : ℝ)))^(4539/1024 : ℝ) := by
    rw [show (45301188599477495379/45310000000000000000 : ℝ)+(45383095047/45310000000000 : ℝ)*((3871/25000 : ℝ)+(10953/100000 : ℝ))=(10000703272636299/10000000000000000 : ℝ) by norm_num, show 1+(25648512490651323/100000000000000000000 : ℝ)+(2764317102672239/50000000000000000000 : ℝ)=(100031177146695995801/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25648512490651323/100000000000000000000 : ℝ) ≤ ((45301188599477495379/45310000000000000000 : ℝ)+2*(45383095047/45310000000000 : ℝ)*(3871/25000 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (45301188599477495379/45310000000000000000 : ℝ)+2*(45383095047/45310000000000 : ℝ)*(3871/25000 : ℝ)=(10001157103586769/10000000000000000 : ℝ) by norm_num, show 1+2*(25648512490651323/100000000000000000000 : ℝ)=(50025648512490651323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45301188599477495379/45310000000000000000 : ℝ)*(X 1 0+X 2 0)+(45383095047/45310000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (10953/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (45301188599477495379/45310000000000000000 : ℝ)) (alpha := (45383095047/45310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45301188599477495379/45310000000000000000 : ℝ)*(X 0 1+X 2 1)+(45383095047/45310000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (10953/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (45301188599477495379/45310000000000000000 : ℝ)) (alpha := (45383095047/45310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45301188599477495379/45310000000000000000 : ℝ)*(X 0 2+X 1 2)+(45383095047/45310000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (10953/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (45301188599477495379/45310000000000000000 : ℝ)) (alpha := (45383095047/45310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-926672653/5000000000 : ℝ)*X 0 0+(5431935967/10000000000 : ℝ)*X 0 1+(5218124999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337757227/2500000000 : ℝ)*X 1 0+(-1962826937/10000000000 : ℝ)*X 1 1+(1043625023/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675514469/5000000000 : ℝ)*X 2 0+(1043625007/2000000000 : ℝ)*X 2 1+(-490706751/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1066284471/2500000000 : ℝ)*X 0 0+(1006723523/2500000000 : ℝ)*X 0 1+(56439339/125000000 : ℝ)*X 0 2+(1066284471/2500000000 : ℝ)*X 1 0+(1006723523/2500000000 : ℝ)*X 1 1+(56439339/125000000 : ℝ)*X 1 2+(1066284471/2500000000 : ℝ)*X 2 0+(1006723523/2500000000 : ℝ)*X 2 1+(56439339/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-926686689/5000000000 : ℝ)*X 0 0+(208769121/400000000 : ℝ)*X 0 1+(5430825171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294817827/10000000000 : ℝ)*X 1 0+(-1750126889/10000000000 : ℝ)*X 1 1+(5430825047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294817481/10000000000 : ℝ)*X 2 0+(678853143/1250000000 : ℝ)*X 2 1+(-1750127231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4265200869/10000000000 : ℝ)*X 0 0+(2256315141/5000000000 : ℝ)*X 0 1+(4029431713/10000000000 : ℝ)*X 0 2+(4265200869/10000000000 : ℝ)*X 1 0+(2256315141/5000000000 : ℝ)*X 1 1+(4029431713/10000000000 : ℝ)*X 1 2+(4265200869/10000000000 : ℝ)*X 2 0+(2256315141/5000000000 : ℝ)*X 2 1+(4029431713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15143546411268029781353501391/2265500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582777913/50000000000000 : ℝ)*(base19) + (111686513/10000000000000 : ℝ)*(base23) + (40085727/100000000000000 : ℝ)*(lower2) + (233893003/100000000000000 : ℝ)*(upper3) + (118882009/100000000000000 : ℝ)*(upper5) + (3362601032117543/100000000000000 : ℝ)*(major0) + (3362601032117543/100000000000000 : ℝ)*(major1) + (420325129014693/12500000000000 : ℝ)*(major2) + (584631082089791/12500000000000 : ℝ)*(sp0) + (935413049853317/20000000000000 : ℝ)*(sp1) + (4677065297957281/100000000000000 : ℝ)*(sp2) + (81925043809489/4000000000000 : ℝ)*(sp3) + (8879052041/50000000000000 : ℝ)*(sp4) + (2332840387/25000000000000 : ℝ)*(sp7) + (2048135426598773/100000000000000 : ℝ)*(f.failure) + (4677066414822411/100000000000000 : ℝ)*(f.sum) + (10311190564099/4531000000000000000000000000 : ℝ)*base66 + (9131134293613333797/4531000000000000000000000000000000 : ℝ)*base67 + (2434464549550978647/566375000000000000000000000000000 : ℝ)*base69 + (3619479540116666203/4531000000000000000000000000000000 : ℝ)*base72 + (236822628149/141593750000000000000000000 : ℝ)*base73 + (7826581106012896353/566375000000000000000000000000000 : ℝ)*base76 + (52533321536501666203/4531000000000000000000000000000000 : ℝ)*base78 + (57311652428812666203/4531000000000000000000000000000000 : ℝ)*base80 + (3729935896721/2265500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (63000131/10000000000000000000000 : ℝ)*base89 + (63000131/10000000000000000000000 : ℝ)*base91 + (36999869/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1322320637924569302427021389/141593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15111597/20000000000000 : ℝ)*(base19) + (12187849/25000000000000 : ℝ)*(base23) + (161881361/100000000000000 : ℝ)*(upper2) + (6019509/25000000000000 : ℝ)*(lower3) + (1666517/12500000000000 : ℝ)*(upper4) + (25693409/12500000000000 : ℝ)*(lower5) + (424718422174603/12500000000000 : ℝ)*(major0) + (424718422174603/12500000000000 : ℝ)*(major1) + (424718422174603/12500000000000 : ℝ)*(major2) + (137890087/100000000000000 : ℝ)*(sp2) + (295371977365769/6250000000000 : ℝ)*(sp4) + (4725951562294319/100000000000000 : ℝ)*(sp5) + (4725951451210821/100000000000000 : ℝ)*(sp6) + (2069542805646841/100000000000000 : ℝ)*(sp7) + (2069542805646841/100000000000000 : ℝ)*(f.failure) + (295371977365769/6250000000000 : ℝ)*(f.sum) + (36589615764471/4531000000000000000000000000 : ℝ)*base66 + (8817322676076909537/566375000000000000000000000000000 : ℝ)*base67 + (3954339786451284537/566375000000000000000000000000000 : ℝ)*base69 + (8249774781416909537/566375000000000000000000000000000 : ℝ)*base71 + (131443294149/906200000000000000000000000 : ℝ)*base74 + (1407795141646090463/566375000000000000000000000000000 : ℝ)*base76 + (3613726551602659537/566375000000000000000000000000000 : ℝ)*base77 + (244052382047034537/566375000000000000000000000000000 : ℝ)*base79 + (10043310518401/2265500000000000000000000000 : ℝ)*base81 + (84795873/10000000000000000000000 : ℝ)*base90 + (84795873/10000000000000000000000 : ℝ)*base92 + (84795873/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1522_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10953/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1522_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1522_box_0 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1641489229/10000000000 : ℝ)*x 0 + (2700876229/5000000000 : ℝ)*x 1 + (675219037/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1641489229/10000000000 : ℝ)^4541 ≤ (4849745151261/50000000000000 : ℝ)^3517 := by
    have hnat : (1641489229 : ℕ)^4541*50000000000000^3517 ≤ 4849745151261^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641489229 10000000000 4849745151261 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700876229/5000000000 : ℝ)^4541 ≤ (45150255713907/100000000000000 : ℝ)^3517 := by
    have hnat : (2700876229 : ℕ)^4541*100000000000000^3517 ≤ 45150255713907^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700876229 5000000000 45150255713907 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675219037/1250000000 : ℝ)^4541 ≤ (5643781745699/12500000000000 : ℝ)^3517 := by
    have hnat : (675219037 : ℕ)^4541*12500000000000^3517 ≤ 5643781745699^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675219037 1250000000 5643781745699 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1641489229/10000000000 : ℝ), (2700876229/5000000000 : ℝ), (675219037/1250000000 : ℝ)] ![(4849745151261/50000000000000 : ℝ), (45150255713907/100000000000000 : ℝ), (5643781745699/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1641489229/10000000000 : ℝ)|^4541 ≤ (4849745151261/50000000000000 : ℝ)^3517
        have hw : |(-1641489229/10000000000 : ℝ)|=(1641489229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700876229/5000000000 : ℝ)|^4541 ≤ (45150255713907/100000000000000 : ℝ)^3517
        have hw : |(2700876229/5000000000 : ℝ)|=(2700876229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675219037/1250000000 : ℝ)|^4541 ≤ (5643781745699/12500000000000 : ℝ)^3517
        have hw : |(675219037/1250000000 : ℝ)|=(675219037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_1 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317723909/2500000000 : ℝ)*x 0 + (-911542589/5000000000 : ℝ)*x 1 + (2700875391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317723909/2500000000 : ℝ)^4541 ≤ (43743049164927/100000000000000 : ℝ)^3517 := by
    have hnat : (1317723909 : ℕ)^4541*100000000000000^3517 ≤ 43743049164927^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317723909 2500000000 43743049164927 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911542589/5000000000 : ℝ)^4541 ≤ (11106713202007/100000000000000 : ℝ)^3517 := by
    have hnat : (911542589 : ℕ)^4541*100000000000000^3517 ≤ 11106713202007^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911542589 5000000000 11106713202007 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700875391/5000000000 : ℝ)^4541 ≤ (22575118813201/50000000000000 : ℝ)^3517 := by
    have hnat : (2700875391 : ℕ)^4541*50000000000000^3517 ≤ 22575118813201^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700875391 5000000000 22575118813201 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317723909/2500000000 : ℝ), (-911542589/5000000000 : ℝ), (2700875391/5000000000 : ℝ)] ![(43743049164927/100000000000000 : ℝ), (11106713202007/100000000000000 : ℝ), (22575118813201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317723909/2500000000 : ℝ)|^4541 ≤ (43743049164927/100000000000000 : ℝ)^3517
        have hw : |(1317723909/2500000000 : ℝ)|=(1317723909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-911542589/5000000000 : ℝ)|^4541 ≤ (11106713202007/100000000000000 : ℝ)^3517
        have hw : |(-911542589/5000000000 : ℝ)|=(911542589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700875391/5000000000 : ℝ)|^4541 ≤ (22575118813201/50000000000000 : ℝ)^3517
        have hw : |(2700875391/5000000000 : ℝ)|=(2700875391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_2 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054179003/2000000000 : ℝ)*x 0 + (5401751209/10000000000 : ℝ)*x 1 + (-455771359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054179003/2000000000 : ℝ)^4541 ≤ (21871521255367/50000000000000 : ℝ)^3517 := by
    have hnat : (1054179003 : ℕ)^4541*50000000000000^3517 ≤ 21871521255367^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054179003 2000000000 21871521255367 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401751209/10000000000 : ℝ)^4541 ≤ (22575121117307/50000000000000 : ℝ)^3517 := by
    have hnat : (5401751209 : ℕ)^4541*50000000000000^3517 ≤ 22575121117307^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401751209 10000000000 22575121117307 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455771359/2500000000 : ℝ)^4541 ≤ (11106715231453/100000000000000 : ℝ)^3517 := by
    have hnat : (455771359 : ℕ)^4541*100000000000000^3517 ≤ 11106715231453^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455771359 2500000000 11106715231453 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054179003/2000000000 : ℝ), (5401751209/10000000000 : ℝ), (-455771359/2500000000 : ℝ)] ![(21871521255367/50000000000000 : ℝ), (22575121117307/50000000000000 : ℝ), (11106715231453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054179003/2000000000 : ℝ)|^4541 ≤ (21871521255367/50000000000000 : ℝ)^3517
        have hw : |(1054179003/2000000000 : ℝ)|=(1054179003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401751209/10000000000 : ℝ)|^4541 ≤ (22575121117307/50000000000000 : ℝ)^3517
        have hw : |(5401751209/10000000000 : ℝ)|=(5401751209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-455771359/2500000000 : ℝ)|^4541 ≤ (11106715231453/100000000000000 : ℝ)^3517
        have hw : |(-455771359/2500000000 : ℝ)|=(455771359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_3 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (279234757/625000000 : ℝ)*x 0 + (4170746739/10000000000 : ℝ)*x 1 + (4170747107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279234757/625000000 : ℝ)^4541 ≤ (17667718681641/50000000000000 : ℝ)^3517 := by
    have hnat : (279234757 : ℕ)^4541*50000000000000^3517 ≤ 17667718681641^3517*625000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279234757 625000000 17667718681641 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170746739/10000000000 : ℝ)^4541 ≤ (4041534933683/12500000000000 : ℝ)^3517 := by
    have hnat : (4170746739 : ℕ)^4541*12500000000000^3517 ≤ 4041534933683^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170746739 10000000000 4041534933683 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170747107/10000000000 : ℝ)^4541 ≤ (32332283152869/100000000000000 : ℝ)^3517 := by
    have hnat : (4170747107 : ℕ)^4541*100000000000000^3517 ≤ 32332283152869^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170747107 10000000000 32332283152869 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279234757/625000000 : ℝ), (4170746739/10000000000 : ℝ), (4170747107/10000000000 : ℝ)] ![(17667718681641/50000000000000 : ℝ), (4041534933683/12500000000000 : ℝ), (32332283152869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279234757/625000000 : ℝ)|^4541 ≤ (17667718681641/50000000000000 : ℝ)^3517
        have hw : |(279234757/625000000 : ℝ)|=(279234757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170746739/10000000000 : ℝ)|^4541 ≤ (4041534933683/12500000000000 : ℝ)^3517
        have hw : |(4170746739/10000000000 : ℝ)|=(4170746739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170747107/10000000000 : ℝ)|^4541 ≤ (32332283152869/100000000000000 : ℝ)^3517
        have hw : |(4170747107/10000000000 : ℝ)|=(4170747107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_4 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035316211/5000000000 : ℝ)*x 0 + (1048787041/2000000000 : ℝ)*x 1 + (2621967053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035316211/5000000000 : ℝ)^4541 ≤ (13091260123609/100000000000000 : ℝ)^3517 := by
    have hnat : (1035316211 : ℕ)^4541*100000000000000^3517 ≤ 13091260123609^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035316211 5000000000 13091260123609 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048787041/2000000000 : ℝ)^4541 ≤ (169743655509/390625000000 : ℝ)^3517 := by
    have hnat : (1048787041 : ℕ)^4541*390625000000^3517 ≤ 169743655509^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048787041 2000000000 169743655509 390625000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621967053/5000000000 : ℝ)^4541 ≤ (1738174562071/4000000000000 : ℝ)^3517 := by
    have hnat : (2621967053 : ℕ)^4541*4000000000000^3517 ≤ 1738174562071^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621967053 5000000000 1738174562071 4000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035316211/5000000000 : ℝ), (1048787041/2000000000 : ℝ), (2621967053/5000000000 : ℝ)] ![(13091260123609/100000000000000 : ℝ), (169743655509/390625000000 : ℝ), (1738174562071/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035316211/5000000000 : ℝ)|^4541 ≤ (13091260123609/100000000000000 : ℝ)^3517
        have hw : |(-1035316211/5000000000 : ℝ)|=(1035316211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048787041/2000000000 : ℝ)|^4541 ≤ (169743655509/390625000000 : ℝ)^3517
        have hw : |(1048787041/2000000000 : ℝ)|=(1048787041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621967053/5000000000 : ℝ)|^4541 ≤ (1738174562071/4000000000000 : ℝ)^3517
        have hw : |(2621967053/5000000000 : ℝ)|=(2621967053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_5 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380685537/10000000000 : ℝ)*x 0 + (-1888331471/10000000000 : ℝ)*x 1 + (5243935033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380685537/10000000000 : ℝ)^4541 ≤ (44923029274069/100000000000000 : ℝ)^3517 := by
    have hnat : (5380685537 : ℕ)^4541*100000000000000^3517 ≤ 44923029274069^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380685537 10000000000 44923029274069 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1888331471/10000000000 : ℝ)^4541 ≤ (11622596739261/100000000000000 : ℝ)^3517 := by
    have hnat : (1888331471 : ℕ)^4541*100000000000000^3517 ≤ 11622596739261^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888331471 10000000000 11622596739261 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243935033/10000000000 : ℝ)^4541 ≤ (1738174958801/4000000000000 : ℝ)^3517 := by
    have hnat : (5243935033 : ℕ)^4541*4000000000000^3517 ≤ 1738174958801^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243935033 10000000000 1738174958801 4000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380685537/10000000000 : ℝ), (-1888331471/10000000000 : ℝ), (5243935033/10000000000 : ℝ)] ![(44923029274069/100000000000000 : ℝ), (11622596739261/100000000000000 : ℝ), (1738174958801/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380685537/10000000000 : ℝ)|^4541 ≤ (44923029274069/100000000000000 : ℝ)^3517
        have hw : |(5380685537/10000000000 : ℝ)|=(5380685537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1888331471/10000000000 : ℝ)|^4541 ≤ (11622596739261/100000000000000 : ℝ)^3517
        have hw : |(-1888331471/10000000000 : ℝ)|=(1888331471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243935033/10000000000 : ℝ)|^4541 ≤ (1738174958801/4000000000000 : ℝ)^3517
        have hw : |(5243935033/10000000000 : ℝ)|=(5243935033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_6 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076137193/2000000000 : ℝ)*x 0 + (655491827/1250000000 : ℝ)*x 1 + (-472082863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076137193/2000000000 : ℝ)^4541 ≤ (22461516943911/50000000000000 : ℝ)^3517 := by
    have hnat : (1076137193 : ℕ)^4541*50000000000000^3517 ≤ 22461516943911^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076137193 2000000000 22461516943911 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655491827/1250000000 : ℝ)^4541 ≤ (43454369508417/100000000000000 : ℝ)^3517 := by
    have hnat : (655491827 : ℕ)^4541*100000000000000^3517 ≤ 43454369508417^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655491827 1250000000 43454369508417 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472082863/2500000000 : ℝ)^4541 ≤ (11622596588267/100000000000000 : ℝ)^3517 := by
    have hnat : (472082863 : ℕ)^4541*100000000000000^3517 ≤ 11622596588267^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472082863 2500000000 11622596588267 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076137193/2000000000 : ℝ), (655491827/1250000000 : ℝ), (-472082863/2500000000 : ℝ)] ![(22461516943911/50000000000000 : ℝ), (43454369508417/100000000000000 : ℝ), (11622596588267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076137193/2000000000 : ℝ)|^4541 ≤ (22461516943911/50000000000000 : ℝ)^3517
        have hw : |(1076137193/2000000000 : ℝ)|=(1076137193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655491827/1250000000 : ℝ)|^4541 ≤ (43454369508417/100000000000000 : ℝ)^3517
        have hw : |(655491827/1250000000 : ℝ)|=(655491827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-472082863/2500000000 : ℝ)|^4541 ≤ (11622596588267/100000000000000 : ℝ)^3517
        have hw : |(-472082863/2500000000 : ℝ)|=(472082863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_7 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (31719163/78125000 : ℝ)*x 0 + (4374465677/10000000000 : ℝ)*x 1 + (1093616349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31719163/78125000 : ℝ)^4541 ≤ (31228624570659/100000000000000 : ℝ)^3517 := by
    have hnat : (31719163 : ℕ)^4541*100000000000000^3517 ≤ 31228624570659^3517*78125000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31719163 78125000 31228624570659 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4374465677/10000000000 : ℝ)^4541 ≤ (8596422283067/25000000000000 : ℝ)^3517 := by
    have hnat : (4374465677 : ℕ)^4541*25000000000000^3517 ≤ 8596422283067^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374465677 10000000000 8596422283067 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093616349/2500000000 : ℝ)^4541 ≤ (34385686280343/100000000000000 : ℝ)^3517 := by
    have hnat : (1093616349 : ℕ)^4541*100000000000000^3517 ≤ 34385686280343^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093616349 2500000000 34385686280343 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31719163/78125000 : ℝ), (4374465677/10000000000 : ℝ), (1093616349/2500000000 : ℝ)] ![(31228624570659/100000000000000 : ℝ), (8596422283067/25000000000000 : ℝ), (34385686280343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31719163/78125000 : ℝ)|^4541 ≤ (31228624570659/100000000000000 : ℝ)^3517
        have hw : |(31719163/78125000 : ℝ)|=(31719163/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4374465677/10000000000 : ℝ)|^4541 ≤ (8596422283067/25000000000000 : ℝ)^3517
        have hw : |(4374465677/10000000000 : ℝ)|=(4374465677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093616349/2500000000 : ℝ)|^4541 ≤ (34385686280343/100000000000000 : ℝ)^3517
        have hw : |(1093616349/2500000000 : ℝ)|=(1093616349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_8 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-247486547/1250000000 : ℝ)*x 0 + (5133262207/10000000000 : ℝ)*x 1 + (108443503/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247486547/1250000000 : ℝ)^4541 ≤ (12355311253833/100000000000000 : ℝ)^3517 := by
    have hnat : (247486547 : ℕ)^4541*100000000000000^3517 ≤ 12355311253833^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247486547 1250000000 12355311253833 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133262207/10000000000 : ℝ)^4541 ≤ (2113695436733/5000000000000 : ℝ)^3517 := by
    have hnat : (5133262207 : ℕ)^4541*5000000000000^3517 ≤ 2113695436733^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133262207 10000000000 2113695436733 5000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108443503/200000000 : ℝ)^4541 ≤ (5671347499241/12500000000000 : ℝ)^3517 := by
    have hnat : (108443503 : ℕ)^4541*12500000000000^3517 ≤ 5671347499241^3517*200000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108443503 200000000 5671347499241 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247486547/1250000000 : ℝ), (5133262207/10000000000 : ℝ), (108443503/200000000 : ℝ)] ![(12355311253833/100000000000000 : ℝ), (2113695436733/5000000000000 : ℝ), (5671347499241/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247486547/1250000000 : ℝ)|^4541 ≤ (12355311253833/100000000000000 : ℝ)^3517
        have hw : |(-247486547/1250000000 : ℝ)|=(247486547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133262207/10000000000 : ℝ)|^4541 ≤ (2113695436733/5000000000000 : ℝ)^3517
        have hw : |(5133262207/10000000000 : ℝ)|=(5133262207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108443503/200000000 : ℝ)|^4541 ≤ (5671347499241/12500000000000 : ℝ)^3517
        have hw : |(108443503/200000000 : ℝ)|=(108443503/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_9 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314170227/2500000000 : ℝ)*x 0 + (-1814397941/10000000000 : ℝ)*x 1 + (2711087557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314170227/2500000000 : ℝ)^4541 ≤ (21795397062743/50000000000000 : ℝ)^3517 := by
    have hnat : (1314170227 : ℕ)^4541*50000000000000^3517 ≤ 21795397062743^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314170227 2500000000 21795397062743 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1814397941/10000000000 : ℝ)^4541 ≤ (11038426256713/100000000000000 : ℝ)^3517 := by
    have hnat : (1814397941 : ℕ)^4541*100000000000000^3517 ≤ 11038426256713^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814397941 10000000000 11038426256713 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711087557/5000000000 : ℝ)^4541 ≤ (22685389802493/50000000000000 : ℝ)^3517 := by
    have hnat : (2711087557 : ℕ)^4541*50000000000000^3517 ≤ 22685389802493^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711087557 5000000000 22685389802493 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314170227/2500000000 : ℝ), (-1814397941/10000000000 : ℝ), (2711087557/5000000000 : ℝ)] ![(21795397062743/50000000000000 : ℝ), (11038426256713/100000000000000 : ℝ), (22685389802493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314170227/2500000000 : ℝ)|^4541 ≤ (21795397062743/50000000000000 : ℝ)^3517
        have hw : |(1314170227/2500000000 : ℝ)|=(1314170227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1814397941/10000000000 : ℝ)|^4541 ≤ (11038426256713/100000000000000 : ℝ)^3517
        have hw : |(-1814397941/10000000000 : ℝ)|=(1814397941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711087557/5000000000 : ℝ)|^4541 ≤ (22685389802493/50000000000000 : ℝ)^3517
        have hw : |(2711087557/5000000000 : ℝ)|=(2711087557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_10 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256680889/10000000000 : ℝ)*x 0 + (2711087573/5000000000 : ℝ)*x 1 + (-453599481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256680889/10000000000 : ℝ)^4541 ≤ (8718158784411/20000000000000 : ℝ)^3517 := by
    have hnat : (5256680889 : ℕ)^4541*20000000000000^3517 ≤ 8718158784411^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256680889 10000000000 8718158784411 20000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711087573/5000000000 : ℝ)^4541 ≤ (5671347493839/12500000000000 : ℝ)^3517 := by
    have hnat : (2711087573 : ℕ)^4541*12500000000000^3517 ≤ 5671347493839^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711087573 5000000000 5671347493839 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453599481/2500000000 : ℝ)^4541 ≤ (441537044927/4000000000000 : ℝ)^3517 := by
    have hnat : (453599481 : ℕ)^4541*4000000000000^3517 ≤ 441537044927^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453599481 2500000000 441537044927 4000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256680889/10000000000 : ℝ), (2711087573/5000000000 : ℝ), (-453599481/2500000000 : ℝ)] ![(8718158784411/20000000000000 : ℝ), (5671347493839/12500000000000 : ℝ), (441537044927/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256680889/10000000000 : ℝ)|^4541 ≤ (8718158784411/20000000000000 : ℝ)^3517
        have hw : |(5256680889/10000000000 : ℝ)|=(5256680889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711087573/5000000000 : ℝ)|^4541 ≤ (5671347493839/12500000000000 : ℝ)^3517
        have hw : |(2711087573/5000000000 : ℝ)|=(2711087573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-453599481/2500000000 : ℝ)|^4541 ≤ (441537044927/4000000000000 : ℝ)^3517
        have hw : |(-453599481/2500000000 : ℝ)|=(453599481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_11 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4519365443/10000000000 : ℝ)*x 0 + (828870331/2000000000 : ℝ)*x 1 + (2072175869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4519365443/10000000000 : ℝ)^4541 ≤ (35863342776669/100000000000000 : ℝ)^3517 := by
    have hnat : (4519365443 : ℕ)^4541*100000000000000^3517 ≤ 35863342776669^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519365443 10000000000 35863342776669 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828870331/2000000000 : ℝ)^4541 ≤ (32068328183973/100000000000000 : ℝ)^3517 := by
    have hnat : (828870331 : ℕ)^4541*100000000000000^3517 ≤ 32068328183973^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828870331 2000000000 32068328183973 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072175869/5000000000 : ℝ)^4541 ≤ (32068329013207/100000000000000 : ℝ)^3517 := by
    have hnat : (2072175869 : ℕ)^4541*100000000000000^3517 ≤ 32068329013207^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072175869 5000000000 32068329013207 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4519365443/10000000000 : ℝ), (828870331/2000000000 : ℝ), (2072175869/5000000000 : ℝ)] ![(35863342776669/100000000000000 : ℝ), (32068328183973/100000000000000 : ℝ), (32068329013207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4519365443/10000000000 : ℝ)|^4541 ≤ (35863342776669/100000000000000 : ℝ)^3517
        have hw : |(4519365443/10000000000 : ℝ)|=(4519365443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828870331/2000000000 : ℝ)|^4541 ≤ (32068328183973/100000000000000 : ℝ)^3517
        have hw : |(828870331/2000000000 : ℝ)|=(828870331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072175869/5000000000 : ℝ)|^4541 ≤ (32068329013207/100000000000000 : ℝ)^3517
        have hw : |(2072175869/5000000000 : ℝ)|=(2072175869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_12 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1732125953/10000000000 : ℝ)*x 0 + (2754450443/5000000000 : ℝ)*x 1 + (5228900887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1732125953/10000000000 : ℝ)^4541 ≤ (5198240586537/50000000000000 : ℝ)^3517 := by
    have hnat : (1732125953 : ℕ)^4541*50000000000000^3517 ≤ 5198240586537^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732125953 10000000000 5198240586537 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754450443/5000000000 : ℝ)^4541 ≤ (46309932481967/100000000000000 : ℝ)^3517 := by
    have hnat : (2754450443 : ℕ)^4541*100000000000000^3517 ≤ 46309932481967^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754450443 5000000000 46309932481967 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228900887/10000000000 : ℝ)^4541 ≤ (346348690611/800000000000 : ℝ)^3517 := by
    have hnat : (5228900887 : ℕ)^4541*800000000000^3517 ≤ 346348690611^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228900887 10000000000 346348690611 800000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1732125953/10000000000 : ℝ), (2754450443/5000000000 : ℝ), (5228900887/10000000000 : ℝ)] ![(5198240586537/50000000000000 : ℝ), (46309932481967/100000000000000 : ℝ), (346348690611/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1732125953/10000000000 : ℝ)|^4541 ≤ (5198240586537/50000000000000 : ℝ)^3517
        have hw : |(-1732125953/10000000000 : ℝ)|=(1732125953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754450443/5000000000 : ℝ)|^4541 ≤ (46309932481967/100000000000000 : ℝ)^3517
        have hw : |(2754450443/5000000000 : ℝ)|=(2754450443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228900887/10000000000 : ℝ)|^4541 ≤ (346348690611/800000000000 : ℝ)^3517
        have hw : |(5228900887/10000000000 : ℝ)|=(5228900887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_13 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695572301/5000000000 : ℝ)*x 0 + (-947184869/5000000000 : ℝ)*x 1 + (5228900947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695572301/5000000000 : ℝ)^4541 ≤ (45035807754977/100000000000000 : ℝ)^3517 := by
    have hnat : (2695572301 : ℕ)^4541*100000000000000^3517 ≤ 45035807754977^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695572301 5000000000 45035807754977 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947184869/5000000000 : ℝ)^4541 ≤ (1167060526337/10000000000000 : ℝ)^3517 := by
    have hnat : (947184869 : ℕ)^4541*10000000000000^3517 ≤ 1167060526337^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947184869 5000000000 1167060526337 10000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228900947/10000000000 : ℝ)^4541 ≤ (43293586967797/100000000000000 : ℝ)^3517 := by
    have hnat : (5228900947 : ℕ)^4541*100000000000000^3517 ≤ 43293586967797^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228900947 10000000000 43293586967797 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695572301/5000000000 : ℝ), (-947184869/5000000000 : ℝ), (5228900947/10000000000 : ℝ)] ![(45035807754977/100000000000000 : ℝ), (1167060526337/10000000000000 : ℝ), (43293586967797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695572301/5000000000 : ℝ)|^4541 ≤ (45035807754977/100000000000000 : ℝ)^3517
        have hw : |(2695572301/5000000000 : ℝ)|=(2695572301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-947184869/5000000000 : ℝ)|^4541 ≤ (1167060526337/10000000000000 : ℝ)^3517
        have hw : |(-947184869/5000000000 : ℝ)|=(947184869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228900947/10000000000 : ℝ)|^4541 ≤ (43293586967797/100000000000000 : ℝ)^3517
        have hw : |(5228900947/10000000000 : ℝ)|=(5228900947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_14 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391144577/10000000000 : ℝ)*x 0 + (209156039/400000000 : ℝ)*x 1 + (-947184867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391144577/10000000000 : ℝ)^4541 ≤ (45035807485329/100000000000000 : ℝ)^3517 := by
    have hnat : (5391144577 : ℕ)^4541*100000000000000^3517 ≤ 45035807485329^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391144577 10000000000 45035807485329 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209156039/400000000 : ℝ)^4541 ≤ (43293587267127/100000000000000 : ℝ)^3517 := by
    have hnat : (209156039 : ℕ)^4541*100000000000000^3517 ≤ 43293587267127^3517*400000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209156039 400000000 43293587267127 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947184867/5000000000 : ℝ)^4541 ≤ (182353206743/1562500000000 : ℝ)^3517 := by
    have hnat : (947184867 : ℕ)^4541*1562500000000^3517 ≤ 182353206743^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947184867 5000000000 182353206743 1562500000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391144577/10000000000 : ℝ), (209156039/400000000 : ℝ), (-947184867/5000000000 : ℝ)] ![(45035807485329/100000000000000 : ℝ), (43293587267127/100000000000000 : ℝ), (182353206743/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391144577/10000000000 : ℝ)|^4541 ≤ (45035807485329/100000000000000 : ℝ)^3517
        have hw : |(5391144577/10000000000 : ℝ)|=(5391144577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209156039/400000000 : ℝ)|^4541 ≤ (43293587267127/100000000000000 : ℝ)^3517
        have hw : |(209156039/400000000 : ℝ)|=(209156039/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947184867/5000000000 : ℝ)|^4541 ≤ (182353206743/1562500000000 : ℝ)^3517
        have hw : |(-947184867/5000000000 : ℝ)|=(947184867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_box_15 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1005088281/2500000000 : ℝ)*x 0 + (549231111/1250000000 : ℝ)*x 1 + (274615541/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005088281/2500000000 : ℝ)^4541 ≤ (15417461170219/50000000000000 : ℝ)^3517 := by
    have hnat : (1005088281 : ℕ)^4541*50000000000000^3517 ≤ 15417461170219^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005088281 2500000000 15417461170219 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549231111/1250000000 : ℝ)^4541 ≤ (540352187533/1562500000000 : ℝ)^3517 := by
    have hnat : (549231111 : ℕ)^4541*1562500000000^3517 ≤ 540352187533^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549231111 1250000000 540352187533 1562500000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274615541/625000000 : ℝ)^4541 ≤ (6916507528893/20000000000000 : ℝ)^3517 := by
    have hnat : (274615541 : ℕ)^4541*20000000000000^3517 ≤ 6916507528893^3517*625000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274615541 625000000 6916507528893 20000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1005088281/2500000000 : ℝ), (549231111/1250000000 : ℝ), (274615541/625000000 : ℝ)] ![(15417461170219/50000000000000 : ℝ), (540352187533/1562500000000 : ℝ), (6916507528893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1005088281/2500000000 : ℝ)|^4541 ≤ (15417461170219/50000000000000 : ℝ)^3517
        have hw : |(1005088281/2500000000 : ℝ)|=(1005088281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549231111/1250000000 : ℝ)|^4541 ≤ (540352187533/1562500000000 : ℝ)^3517
        have hw : |(549231111/1250000000 : ℝ)|=(549231111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274615541/625000000 : ℝ)|^4541 ≤ (6916507528893/20000000000000 : ℝ)^3517
        have hw : |(274615541/625000000 : ℝ)|=(274615541/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1522_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63753/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2347/4000 : ℝ) ∧ (40213/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43033/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5477/50000 : ℝ) ^ (4539/1024 : ℝ) ≤ (276543598148933/5000000000000000000 : ℝ) := by
    have hpowers : (5477/50000 : ℝ)^4539 ≤ (276543598148933/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5477 : ℕ)^4539*5000000000000000000^1024 ≤ 276543598148933^1024*50000^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5477 50000 276543598148933 5000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5477/50000 : ℝ)) (X := (276543598148933/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4539/1024 : ℝ) ≤ (5128234176816643/20000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4539 ≤ (5128234176816643/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4539*20000000000000000000^1024 ≤ 5128234176816643^1024*100000^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 5128234176816643 20000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (5128234176816643/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500276543598148933/2500000000000000000 : ℝ) ≤ (2500062385661241/2500000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (2500276543598148933/2500000000000000000 : ℝ)^1024 ≤ (2500062385661241/2500000000000000 : ℝ)^4539 := by
      have hnat : (2500276543598148933 : ℕ)^1024*2500000000000000^4539 ≤ 2500062385661241^4539*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500276543598148933 2500000000000000000 2500062385661241 2500000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500062385661241/2500000000000000 : ℝ)) (X := (2500276543598148933/2500000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (160049875268555299/160000000000000000 : ℝ) ≤ (2500175789380269/2500000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (160049875268555299/160000000000000000 : ℝ)^1024 ≤ (2500175789380269/2500000000000000 : ℝ)^4539 := by
      have hnat : (160049875268555299 : ℕ)^1024*2500000000000000^4539 ≤ 2500175789380269^4539*160000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160049875268555299 160000000000000000 2500175789380269 2500000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500175789380269/2500000000000000 : ℝ)) (X := (160049875268555299/160000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005128234176816643/10000000000000000000 : ℝ) ≤ (2500289193099297/2500000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (10005128234176816643/10000000000000000000 : ℝ)^1024 ≤ (2500289193099297/2500000000000000 : ℝ)^4539 := by
      have hnat : (10005128234176816643 : ℕ)^1024*2500000000000000^4539 ≤ 2500289193099297^4539*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005128234176816643 10000000000000000000 2500289193099297 2500000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500289193099297/2500000000000000 : ℝ)) (X := (10005128234176816643/10000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(276543598148933/5000000000000000000 : ℝ) ≤ ((2264059619196659013/2264500000000000000 : ℝ)+2*(28350929757/28306250000000 : ℝ)*(5477/50000 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (2264059619196659013/2264500000000000000 : ℝ)+2*(28350929757/28306250000000 : ℝ)*(5477/50000 : ℝ)=(2500062385661241/2500000000000000 : ℝ) by norm_num, show 1+2*(276543598148933/5000000000000000000 : ℝ)=(2500276543598148933/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5128234176816643/20000000000000000000 : ℝ)+(276543598148933/5000000000000000000 : ℝ) ≤ ((2264059619196659013/2264500000000000000 : ℝ)+(28350929757/28306250000000 : ℝ)*((15483/100000 : ℝ)+(5477/50000 : ℝ)))^(4539/1024 : ℝ) := by
    rw [show (2264059619196659013/2264500000000000000 : ℝ)+(28350929757/28306250000000 : ℝ)*((15483/100000 : ℝ)+(5477/50000 : ℝ))=(2500175789380269/2500000000000000 : ℝ) by norm_num, show 1+(5128234176816643/20000000000000000000 : ℝ)+(276543598148933/5000000000000000000 : ℝ)=(160049875268555299/160000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5128234176816643/20000000000000000000 : ℝ) ≤ ((2264059619196659013/2264500000000000000 : ℝ)+2*(28350929757/28306250000000 : ℝ)*(15483/100000 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (2264059619196659013/2264500000000000000 : ℝ)+2*(28350929757/28306250000000 : ℝ)*(15483/100000 : ℝ)=(2500289193099297/2500000000000000 : ℝ) by norm_num, show 1+2*(5128234176816643/20000000000000000000 : ℝ)=(10005128234176816643/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2264059619196659013/2264500000000000000 : ℝ)*(X 1 0+X 2 0)+(28350929757/28306250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (2264059619196659013/2264500000000000000 : ℝ)) (alpha := (28350929757/28306250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2264059619196659013/2264500000000000000 : ℝ)*(X 0 1+X 2 1)+(28350929757/28306250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (2264059619196659013/2264500000000000000 : ℝ)) (alpha := (28350929757/28306250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2264059619196659013/2264500000000000000 : ℝ)*(X 0 2+X 1 2)+(28350929757/28306250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (2264059619196659013/2264500000000000000 : ℝ)) (alpha := (28350929757/28306250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1641489229/10000000000 : ℝ)*X 0 0+(2700876229/5000000000 : ℝ)*X 0 1+(675219037/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317723909/2500000000 : ℝ)*X 1 0+(-911542589/5000000000 : ℝ)*X 1 1+(2700875391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1054179003/2000000000 : ℝ)*X 2 0+(5401751209/10000000000 : ℝ)*X 2 1+(-455771359/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((279234757/625000000 : ℝ)*X 0 0+(4170746739/10000000000 : ℝ)*X 0 1+(4170747107/10000000000 : ℝ)*X 0 2+(279234757/625000000 : ℝ)*X 1 0+(4170746739/10000000000 : ℝ)*X 1 1+(4170747107/10000000000 : ℝ)*X 1 2+(279234757/625000000 : ℝ)*X 2 0+(4170746739/10000000000 : ℝ)*X 2 1+(4170747107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1035316211/5000000000 : ℝ)*X 0 0+(1048787041/2000000000 : ℝ)*X 0 1+(2621967053/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5380685537/10000000000 : ℝ)*X 1 0+(-1888331471/10000000000 : ℝ)*X 1 1+(5243935033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1076137193/2000000000 : ℝ)*X 2 0+(655491827/1250000000 : ℝ)*X 2 1+(-472082863/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((31719163/78125000 : ℝ)*X 0 0+(4374465677/10000000000 : ℝ)*X 0 1+(1093616349/2500000000 : ℝ)*X 0 2+(31719163/78125000 : ℝ)*X 1 0+(4374465677/10000000000 : ℝ)*X 1 1+(1093616349/2500000000 : ℝ)*X 1 2+(31719163/78125000 : ℝ)*X 2 0+(4374465677/10000000000 : ℝ)*X 2 1+(1093616349/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-247486547/1250000000 : ℝ)*X 0 0+(5133262207/10000000000 : ℝ)*X 0 1+(108443503/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314170227/2500000000 : ℝ)*X 1 0+(-1814397941/10000000000 : ℝ)*X 1 1+(2711087557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256680889/10000000000 : ℝ)*X 2 0+(2711087573/5000000000 : ℝ)*X 2 1+(-453599481/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4519365443/10000000000 : ℝ)*X 0 0+(828870331/2000000000 : ℝ)*X 0 1+(2072175869/5000000000 : ℝ)*X 0 2+(4519365443/10000000000 : ℝ)*X 1 0+(828870331/2000000000 : ℝ)*X 1 1+(2072175869/5000000000 : ℝ)*X 1 2+(4519365443/10000000000 : ℝ)*X 2 0+(828870331/2000000000 : ℝ)*X 2 1+(2072175869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1732125953/10000000000 : ℝ)*X 0 0+(2754450443/5000000000 : ℝ)*X 0 1+(5228900887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2695572301/5000000000 : ℝ)*X 1 0+(-947184869/5000000000 : ℝ)*X 1 1+(5228900947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5391144577/10000000000 : ℝ)*X 2 0+(209156039/400000000 : ℝ)*X 2 1+(-947184867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1005088281/2500000000 : ℝ)*X 0 0+(549231111/1250000000 : ℝ)*X 0 1+(274615541/625000000 : ℝ)*X 0 2+(1005088281/2500000000 : ℝ)*X 1 0+(549231111/1250000000 : ℝ)*X 1 1+(274615541/625000000 : ℝ)*X 1 2+(1005088281/2500000000 : ℝ)*X 2 0+(549231111/1250000000 : ℝ)*X 2 1+(274615541/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63753/100000 : ℝ) ≤ (-36090620625931629799751762923089/56612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (810107/100000000000000 : ℝ)*(upper1) + (909859/6250000000000 : ℝ)*(lower2) + (62801299/100000000000000 : ℝ)*(upper4) + (1651523/100000000000000 : ℝ)*(upper5) + (2238136482840549/100000000000000 : ℝ)*(major0) + (2238136482840549/100000000000000 : ℝ)*(major1) + (2238136482840549/100000000000000 : ℝ)*(major2) + (2190570767/100000000000000 : ℝ)*(sp2) + (1567138482668763/50000000000000 : ℝ)*(sp4) + (1567129685165829/50000000000000 : ℝ)*(sp5) + (783572120236659/25000000000000 : ℝ)*(sp6) + (85202023974247/6250000000000 : ℝ)*(sp7) + (13706179877/100000000000000 : ℝ)*(sp8) + (1956324109/6250000000000 : ℝ)*(sp13) + (85202023974247/6250000000000 : ℝ)*(f.failure) + (1567145335758701/50000000000000 : ℝ)*(f.sum) + (16938279799727/5661250000000000000000000000 : ℝ)*base65 + (264003344551527409/32350000000000000000000000000000 : ℝ)*base68 + (62692284500277409/32350000000000000000000000000000 : ℝ)*base70 + (16359044360677409/32350000000000000000000000000000 : ℝ)*base72 + (41162071714521/11322500000000000000000000000 : ℝ)*base74 + (314277219676122591/32350000000000000000000000000000 : ℝ)*base75 + (47589928816527409/32350000000000000000000000000000 : ℝ)*base78 + (191683227970027409/32350000000000000000000000000000 : ℝ)*base80 + (17157057084957/5661250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4053809/625000000000000000000 : ℝ)*base89 + (4053809/625000000000000000000 : ℝ)*base91 + (4053809/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2347/4000 : ℝ) ≤ (66437316243895025349839251142961/113225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16485733/50000000000000 : ℝ)*(upper2) + (124068269/100000000000000 : ℝ)*(lower4) + (11232043/20000000000000 : ℝ)*(lower5) + (2315062805424099/100000000000000 : ℝ)*(major0) + (2315062805424099/100000000000000 : ℝ)*(major1) + (23150628054241/1000000000000 : ℝ)*(major2) + (800118998739637/25000000000000 : ℝ)*(sp0) + (3200266144523629/100000000000000 : ℝ)*(sp1) + (3200295479564791/100000000000000 : ℝ)*(sp2) + (705043175755279/50000000000000 : ℝ)*(sp3) + (257278573/20000000000000 : ℝ)*(sp7) + (106372554001/50000000000000 : ℝ)*(sp9) + (183410066841/100000000000000 : ℝ)*(sp10) + (723668271/25000000000000 : ℝ)*(sp12) + (1410087637903423/100000000000000 : ℝ)*(f.failure) + (200029930601977/6250000000000 : ℝ)*(f.sum) + (539261868409/404375000000000000000000000 : ℝ)*base65 + (1187831334666995713/226450000000000000000000000000000 : ℝ)*base68 + (19226317241229533/2264500000000000000000000000000 : ℝ)*base69 + (1881511290413554287/226450000000000000000000000000000 : ℝ)*base71 + (26132601896313/3235000000000000000000000000 : ℝ)*base74 + (32658338507074533/2264500000000000000000000000000 : ℝ)*base75 + (11115400730757959/32350000000000000000000000000000 : ℝ)*base78 + (61704871040457959/32350000000000000000000000000000 : ℝ)*base80 + (16050357019191/11322500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4808681/10000000000000000000000 : ℝ)*base89 + (4808681/10000000000000000000000 : ℝ)*base91 + (95191319/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40213/50000 : ℝ) ≤ (11383156104378037862522041537449/14153125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2049201/100000000000000 : ℝ)*(upper0) + (3166869/100000000000000 : ℝ)*(lower1) + (892109/25000000000000 : ℝ)*(upper2) + (11507731/100000000000000 : ℝ)*(lower3) + (313469987617191/12500000000000 : ℝ)*(major0) + (313469987617191/12500000000000 : ℝ)*(major1) + (313469987617191/12500000000000 : ℝ)*(major2) + (1008587537/50000000000000 : ℝ)*(sp0) + (2116164569/100000000000000 : ℝ)*(sp2) + (674039531/10000000000000 : ℝ)*(sp3) + (865312561799331/25000000000000 : ℝ)*(sp8) + (1730626132186199/50000000000000 : ℝ)*(sp9) + (865312537051957/25000000000000 : ℝ)*(sp10) + (95465704602549/6250000000000 : ℝ)*(sp11) + (1527458014036093/100000000000000 : ℝ)*(f.failure) + (1730626132186199/50000000000000 : ℝ)*(f.sum) + (22941827895927/11322500000000000000000000000 : ℝ)*base66 + (15881783482851431/4043750000000000000000000000000 : ℝ)*base68 + (2518247966051431/4043750000000000000000000000000 : ℝ)*base70 + (12170760697613931/4043750000000000000000000000000 : ℝ)*base72 + (1036616848199/5661250000000000000000000000 : ℝ)*base73 + (45023458338526431/4043750000000000000000000000000 : ℝ)*base76 + (22036350726004819/4043750000000000000000000000000 : ℝ)*base77 + (43535498521504819/4043750000000000000000000000000 : ℝ)*base79 + (126994497185867/11322500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (42093829/10000000000000000000000 : ℝ)*base90 + (42093829/10000000000000000000000 : ℝ)*base92 + (42093829/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-43033/50000 : ℝ) ≤ (-1740093806252332770400245180639/2021875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30113777/100000000000000 : ℝ)*(lower0) + (230361/12500000000000 : ℝ)*(upper1) + (27357/78125000000 : ℝ)*(upper3) + (6813737/25000000000000 : ℝ)*(upper5) + (318383934861909/12500000000000 : ℝ)*(major0) + (318383934861909/12500000000000 : ℝ)*(major1) + (318383934861909/12500000000000 : ℝ)*(major2) + (724137099/100000000000000 : ℝ)*(sp4) + (2134170407/25000000000000 : ℝ)*(sp5) + (1872690689/25000000000000 : ℝ)*(sp7) + (1785713809433883/50000000000000 : ℝ)*(sp12) + (1785709903161619/50000000000000 : ℝ)*(sp13) + (1785714171502433/50000000000000 : ℝ)*(sp14) + (24240545542959/1562500000000 : ℝ)*(sp15) + (387850601378033/25000000000000 : ℝ)*(f.failure) + (1785714171502433/50000000000000 : ℝ)*(f.sum) + (486696412729/404375000000000000000000000 : ℝ)*base65 + (51315015450245419/4043750000000000000000000000000 : ℝ)*base68 + (48300314086260831/4043750000000000000000000000000 : ℝ)*base69 + (14732538174639169/4043750000000000000000000000000 : ℝ)*base72 + (2073208524593/808750000000000000000000000 : ℝ)*base73 + (275053598061101669/4043750000000000000000000000000 : ℝ)*base76 + (12534501937076669/4043750000000000000000000000000 : ℝ)*base78 + (31622896676576669/4043750000000000000000000000000 : ℝ)*base80 + (5888914381293/808750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6538649/2500000000000000000000 : ℝ)*base90 + (6538649/2500000000000000000000 : ℝ)*base92 + (6538649/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1522_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63753/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2347/4000 : ℝ) else (40213/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43033/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1522_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1522_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10953/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63753/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2347/4000 : ℝ) else (40213/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43033/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1522_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1522_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10953/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63753/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2347/4000 : ℝ) else (40213/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43033/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1522_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
