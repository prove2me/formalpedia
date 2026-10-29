-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1408_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:03.671116+00:00
-- url     : https://prove2.me/submissions/5e25e8e7-14cc-4622-957d-256695cd0c91

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
theorem support_rectangle_w1408_s0_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1770764837/10000000000 : ℝ)*x 0 + (746111913/1250000000 : ℝ)*x 1 + (2413204989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1770764837/10000000000 : ℝ)^273 ≤ (521077894113/5000000000000 : ℝ)^209 := by
    have hnat : (1770764837 : ℕ)^273*5000000000000^209 ≤ 521077894113^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770764837 10000000000 521077894113 5000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746111913/1250000000 : ℝ)^273 ≤ (1592642168499/3125000000000 : ℝ)^209 := by
    have hnat : (746111913 : ℕ)^273*3125000000000^209 ≤ 1592642168499^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746111913 1250000000 1592642168499 3125000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2413204989/5000000000 : ℝ)^273 ≤ (19306946353747/50000000000000 : ℝ)^209 := by
    have hnat : (2413204989 : ℕ)^273*50000000000000^209 ≤ 19306946353747^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2413204989 5000000000 19306946353747 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1770764837/10000000000 : ℝ), (746111913/1250000000 : ℝ), (2413204989/5000000000 : ℝ)] ![(521077894113/5000000000000 : ℝ), (1592642168499/3125000000000 : ℝ), (19306946353747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1770764837/10000000000 : ℝ)|^273 ≤ (521077894113/5000000000000 : ℝ)^209
        have hw : |(-1770764837/10000000000 : ℝ)|=(1770764837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746111913/1250000000 : ℝ)|^273 ≤ (1592642168499/3125000000000 : ℝ)^209
        have hw : |(746111913/1250000000 : ℝ)|=(746111913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2413204989/5000000000 : ℝ)|^273 ≤ (19306946353747/50000000000000 : ℝ)^209
        have hw : |(2413204989/5000000000 : ℝ)|=(2413204989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s0_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5494437401/10000000000 : ℝ)*x 0 + (-241709627/1000000000 : ℝ)*x 1 + (482641027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5494437401/10000000000 : ℝ)^273 ≤ (45738560929123/100000000000000 : ℝ)^209 := by
    have hnat : (5494437401 : ℕ)^273*100000000000000^209 ≤ 45738560929123^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494437401 10000000000 45738560929123 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241709627/1000000000 : ℝ)^273 ≤ (15647543298441/100000000000000 : ℝ)^209 := by
    have hnat : (241709627 : ℕ)^273*100000000000000^209 ≤ 15647543298441^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241709627 1000000000 15647543298441 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482641027/1000000000 : ℝ)^273 ≤ (38613895759031/100000000000000 : ℝ)^209 := by
    have hnat : (482641027 : ℕ)^273*100000000000000^209 ≤ 38613895759031^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482641027 1000000000 38613895759031 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5494437401/10000000000 : ℝ), (-241709627/1000000000 : ℝ), (482641027/1000000000 : ℝ)] ![(45738560929123/100000000000000 : ℝ), (15647543298441/100000000000000 : ℝ), (38613895759031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5494437401/10000000000 : ℝ)|^273 ≤ (45738560929123/100000000000000 : ℝ)^209
        have hw : |(5494437401/10000000000 : ℝ)|=(5494437401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-241709627/1000000000 : ℝ)|^273 ≤ (15647543298441/100000000000000 : ℝ)^209
        have hw : |(-241709627/1000000000 : ℝ)|=(241709627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(482641027/1000000000 : ℝ)|^273 ≤ (38613895759031/100000000000000 : ℝ)^209
        have hw : |(482641027/1000000000 : ℝ)|=(482641027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s0_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2747218809/5000000000 : ℝ)*x 0 + (4826410149/10000000000 : ℝ)*x 1 + (-120854807/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2747218809/5000000000 : ℝ)^273 ≤ (22869281644353/50000000000000 : ℝ)^209 := by
    have hnat : (2747218809 : ℕ)^273*50000000000000^209 ≤ 22869281644353^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747218809 5000000000 22869281644353 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4826410149/10000000000 : ℝ)^273 ≤ (9653473623631/25000000000000 : ℝ)^209 := by
    have hnat : (4826410149 : ℕ)^273*25000000000000^209 ≤ 9653473623631^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826410149 10000000000 9653473623631 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120854807/500000000 : ℝ)^273 ≤ (977971387447/6250000000000 : ℝ)^209 := by
    have hnat : (120854807 : ℕ)^273*6250000000000^209 ≤ 977971387447^209*500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120854807 500000000 977971387447 6250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2747218809/5000000000 : ℝ), (4826410149/10000000000 : ℝ), (-120854807/500000000 : ℝ)] ![(22869281644353/50000000000000 : ℝ), (9653473623631/25000000000000 : ℝ), (977971387447/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2747218809/5000000000 : ℝ)|^273 ≤ (22869281644353/50000000000000 : ℝ)^209
        have hw : |(2747218809/5000000000 : ℝ)|=(2747218809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4826410149/10000000000 : ℝ)|^273 ≤ (9653473623631/25000000000000 : ℝ)^209
        have hw : |(4826410149/10000000000 : ℝ)|=(4826410149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120854807/500000000 : ℝ)|^273 ≤ (977971387447/6250000000000 : ℝ)^209
        have hw : |(-120854807/500000000 : ℝ)|=(120854807/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s0_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (521128501/1250000000 : ℝ)*x 0 + (48498983/156250000 : ℝ)*x 1 + (1389127313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521128501/1250000000 : ℝ)^273 ≤ (31892005974729/100000000000000 : ℝ)^209 := by
    have hnat : (521128501 : ℕ)^273*100000000000000^209 ≤ 31892005974729^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521128501 1250000000 31892005974729 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48498983/156250000 : ℝ)^273 ≤ (21693320630941/100000000000000 : ℝ)^209 := by
    have hnat : (48498983 : ℕ)^273*100000000000000^209 ≤ 21693320630941^209*156250000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48498983 156250000 21693320630941 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389127313/2500000000 : ℝ)^273 ≤ (46414673376887/100000000000000 : ℝ)^209 := by
    have hnat : (1389127313 : ℕ)^273*100000000000000^209 ≤ 46414673376887^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389127313 2500000000 46414673376887 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521128501/1250000000 : ℝ), (48498983/156250000 : ℝ), (1389127313/2500000000 : ℝ)] ![(31892005974729/100000000000000 : ℝ), (21693320630941/100000000000000 : ℝ), (46414673376887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521128501/1250000000 : ℝ)|^273 ≤ (31892005974729/100000000000000 : ℝ)^209
        have hw : |(521128501/1250000000 : ℝ)|=(521128501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48498983/156250000 : ℝ)|^273 ≤ (21693320630941/100000000000000 : ℝ)^209
        have hw : |(48498983/156250000 : ℝ)|=(48498983/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1389127313/2500000000 : ℝ)|^273 ≤ (46414673376887/100000000000000 : ℝ)^209
        have hw : |(1389127313/2500000000 : ℝ)|=(1389127313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s0_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1774884449/10000000000 : ℝ)*x 0 + (4855687259/10000000000 : ℝ)*x 1 + (2969286247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1774884449/10000000000 : ℝ)^273 ≤ (5226619446107/50000000000000 : ℝ)^209 := by
    have hnat : (1774884449 : ℕ)^273*50000000000000^209 ≤ 5226619446107^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774884449 10000000000 5226619446107 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4855687259/10000000000 : ℝ)^273 ≤ (38920137764649/100000000000000 : ℝ)^209 := by
    have hnat : (4855687259 : ℕ)^273*100000000000000^209 ≤ 38920137764649^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4855687259 10000000000 38920137764649 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2969286247/5000000000 : ℝ)^273 ≤ (50626623319683/100000000000000 : ℝ)^209 := by
    have hnat : (2969286247 : ℕ)^273*100000000000000^209 ≤ 50626623319683^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2969286247 5000000000 50626623319683 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1774884449/10000000000 : ℝ), (4855687259/10000000000 : ℝ), (2969286247/5000000000 : ℝ)] ![(5226619446107/50000000000000 : ℝ), (38920137764649/100000000000000 : ℝ), (50626623319683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1774884449/10000000000 : ℝ)|^273 ≤ (5226619446107/50000000000000 : ℝ)^209
        have hw : |(-1774884449/10000000000 : ℝ)|=(1774884449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4855687259/10000000000 : ℝ)|^273 ≤ (38920137764649/100000000000000 : ℝ)^209
        have hw : |(4855687259/10000000000 : ℝ)|=(4855687259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2969286247/5000000000 : ℝ)|^273 ≤ (50626623319683/100000000000000 : ℝ)^209
        have hw : |(2969286247/5000000000 : ℝ)|=(2969286247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s0_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2591353813/5000000000 : ℝ)*x 0 + (-326233593/2500000000 : ℝ)*x 1 + (2969286113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591353813/5000000000 : ℝ)^273 ≤ (42378759283589/100000000000000 : ℝ)^209 := by
    have hnat : (2591353813 : ℕ)^273*100000000000000^209 ≤ 42378759283589^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591353813 5000000000 42378759283589 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326233593/2500000000 : ℝ)^273 ≤ (3497310187927/50000000000000 : ℝ)^209 := by
    have hnat : (326233593 : ℕ)^273*50000000000000^209 ≤ 3497310187927^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326233593 2500000000 3497310187927 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2969286113/5000000000 : ℝ)^273 ≤ (10125324067069/20000000000000 : ℝ)^209 := by
    have hnat : (2969286113 : ℕ)^273*20000000000000^209 ≤ 10125324067069^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2969286113 5000000000 10125324067069 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591353813/5000000000 : ℝ), (-326233593/2500000000 : ℝ), (2969286113/5000000000 : ℝ)] ![(42378759283589/100000000000000 : ℝ), (3497310187927/50000000000000 : ℝ), (10125324067069/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591353813/5000000000 : ℝ)|^273 ≤ (42378759283589/100000000000000 : ℝ)^209
        have hw : |(2591353813/5000000000 : ℝ)|=(2591353813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-326233593/2500000000 : ℝ)|^273 ≤ (3497310187927/50000000000000 : ℝ)^209
        have hw : |(-326233593/2500000000 : ℝ)|=(326233593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2969286113/5000000000 : ℝ)|^273 ≤ (10125324067069/20000000000000 : ℝ)^209
        have hw : |(2969286113/5000000000 : ℝ)|=(2969286113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s0_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (518270771/1000000000 : ℝ)*x 0 + (5938572643/10000000000 : ℝ)*x 1 + (-1304933579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518270771/1000000000 : ℝ)^273 ≤ (8475752036157/20000000000000 : ℝ)^209 := by
    have hnat : (518270771 : ℕ)^273*20000000000000^209 ≤ 8475752036157^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518270771 1000000000 8475752036157 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5938572643/10000000000 : ℝ)^273 ≤ (25313312489443/50000000000000 : ℝ)^209 := by
    have hnat : (5938572643 : ℕ)^273*50000000000000^209 ≤ 25313312489443^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5938572643 10000000000 25313312489443 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304933579/10000000000 : ℝ)^273 ≤ (874326852957/12500000000000 : ℝ)^209 := by
    have hnat : (1304933579 : ℕ)^273*12500000000000^209 ≤ 874326852957^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304933579 10000000000 874326852957 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518270771/1000000000 : ℝ), (5938572643/10000000000 : ℝ), (-1304933579/10000000000 : ℝ)] ![(8475752036157/20000000000000 : ℝ), (25313312489443/50000000000000 : ℝ), (874326852957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518270771/1000000000 : ℝ)|^273 ≤ (8475752036157/20000000000000 : ℝ)^209
        have hw : |(518270771/1000000000 : ℝ)|=(518270771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5938572643/10000000000 : ℝ)|^273 ≤ (25313312489443/50000000000000 : ℝ)^209
        have hw : |(5938572643/10000000000 : ℝ)|=(5938572643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1304933579/10000000000 : ℝ)|^273 ≤ (874326852957/12500000000000 : ℝ)^209
        have hw : |(-1304933579/10000000000 : ℝ)|=(1304933579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s0_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4177873473/10000000000 : ℝ)*x 0 + (5493659299/10000000000 : ℝ)*x 1 + (49516089/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177873473/10000000000 : ℝ)^273 ≤ (3198042079003/10000000000000 : ℝ)^209 := by
    have hnat : (4177873473 : ℕ)^273*10000000000000^209 ≤ 3198042079003^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177873473 10000000000 3198042079003 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493659299/10000000000 : ℝ)^273 ≤ (45730100298363/100000000000000 : ℝ)^209 := by
    have hnat : (5493659299 : ℕ)^273*100000000000000^209 ≤ 45730100298363^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493659299 10000000000 45730100298363 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49516089/156250000 : ℝ)^273 ≤ (11144739451199/50000000000000 : ℝ)^209 := by
    have hnat : (49516089 : ℕ)^273*50000000000000^209 ≤ 11144739451199^209*156250000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49516089 156250000 11144739451199 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177873473/10000000000 : ℝ), (5493659299/10000000000 : ℝ), (49516089/156250000 : ℝ)] ![(3198042079003/10000000000000 : ℝ), (45730100298363/100000000000000 : ℝ), (11144739451199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177873473/10000000000 : ℝ)|^273 ≤ (3198042079003/10000000000000 : ℝ)^209
        have hw : |(4177873473/10000000000 : ℝ)|=(4177873473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493659299/10000000000 : ℝ)|^273 ≤ (45730100298363/100000000000000 : ℝ)^209
        have hw : |(5493659299/10000000000 : ℝ)|=(5493659299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49516089/156250000 : ℝ)|^273 ≤ (11144739451199/50000000000000 : ℝ)^209
        have hw : |(49516089/156250000 : ℝ)|=(49516089/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (949/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6601/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4367/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4367 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4367*1^1024 ≤ 0^1024*1^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4367/1024 : ℝ) ≤ (2008749417333339989/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4367 ≤ (2008749417333339989/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4367*100000000000000000000^1024 ≤ 2008749417333339989^1024*5^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2008749417333339989 100000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2008749417333339989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4367 := by
      have hnat : (1 : ℕ)^1024*1^4367 ≤ 1^4367*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102008749417333339989/100000000000000000000 : ℝ) ≤ (10046744415084987/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (102008749417333339989/100000000000000000000 : ℝ)^1024 ≤ (10046744415084987/10000000000000000 : ℝ)^4367 := by
      have hnat : (102008749417333339989 : ℕ)^1024*10000000000000000^4367 ≤ 10046744415084987^4367*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102008749417333339989 100000000000000000000 10046744415084987 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046744415084987/10000000000000000 : ℝ)) (X := (102008749417333339989/100000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52008749417333339989/50000000000000000000 : ℝ) ≤ (5046744415084987/5000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (52008749417333339989/50000000000000000000 : ℝ)^1024 ≤ (5046744415084987/5000000000000000 : ℝ)^4367 := by
      have hnat : (52008749417333339989 : ℕ)^1024*5000000000000000^4367 ≤ 5046744415084987^4367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52008749417333339989 50000000000000000000 5046744415084987 5000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046744415084987/5000000000000000 : ℝ)) (X := (52008749417333339989/50000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(46744415084987/4000000000000000 : ℝ)*(0 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46744415084987/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2008749417333339989/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(46744415084987/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (1 : ℝ)+(46744415084987/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10046744415084987/10000000000000000 : ℝ) by norm_num, show 1+(2008749417333339989/100000000000000000000 : ℝ)+(0 : ℝ)=(102008749417333339989/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2008749417333339989/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(46744415084987/4000000000000000 : ℝ)*(2/5 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46744415084987/4000000000000000 : ℝ)*(2/5 : ℝ)=(5046744415084987/5000000000000000 : ℝ) by norm_num, show 1+2*(2008749417333339989/100000000000000000000 : ℝ)=(52008749417333339989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(46744415084987/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46744415084987/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(46744415084987/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46744415084987/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(46744415084987/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46744415084987/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1770764837/10000000000 : ℝ)*X 0 0+(746111913/1250000000 : ℝ)*X 0 1+(2413204989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5494437401/10000000000 : ℝ)*X 1 0+(-241709627/1000000000 : ℝ)*X 1 1+(482641027/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2747218809/5000000000 : ℝ)*X 2 0+(4826410149/10000000000 : ℝ)*X 2 1+(-120854807/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((521128501/1250000000 : ℝ)*X 0 0+(48498983/156250000 : ℝ)*X 0 1+(1389127313/2500000000 : ℝ)*X 0 2+(521128501/1250000000 : ℝ)*X 1 0+(48498983/156250000 : ℝ)*X 1 1+(1389127313/2500000000 : ℝ)*X 1 2+(521128501/1250000000 : ℝ)*X 2 0+(48498983/156250000 : ℝ)*X 2 1+(1389127313/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1774884449/10000000000 : ℝ)*X 0 0+(4855687259/10000000000 : ℝ)*X 0 1+(2969286247/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591353813/5000000000 : ℝ)*X 1 0+(-326233593/2500000000 : ℝ)*X 1 1+(2969286113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((518270771/1000000000 : ℝ)*X 2 0+(5938572643/10000000000 : ℝ)*X 2 1+(-1304933579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4177873473/10000000000 : ℝ)*X 0 0+(5493659299/10000000000 : ℝ)*X 0 1+(49516089/156250000 : ℝ)*X 0 2+(4177873473/10000000000 : ℝ)*X 1 0+(5493659299/10000000000 : ℝ)*X 1 1+(49516089/156250000 : ℝ)*X 1 2+(4177873473/10000000000 : ℝ)*X 2 0+(5493659299/10000000000 : ℝ)*X 2 1+(49516089/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (680514953744692560734889/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6315829/100000000000000 : ℝ)*(base1) + (1593915177/100000000000000 : ℝ)*(base19) + (1628484483/100000000000000 : ℝ)*(base23) + (184250947/100000000000000 : ℝ)*(upper3) + (229298013/100000000000000 : ℝ)*(upper5) + (320759124993849/50000000000000 : ℝ)*(major0) + (320759124993849/50000000000000 : ℝ)*(major1) + (320759124993849/50000000000000 : ℝ)*(major2) + (875290083875617/100000000000000 : ℝ)*(sp0) + (875294443976203/100000000000000 : ℝ)*(sp1) + (437647204703449/50000000000000 : ℝ)*(sp2) + (203868757004143/50000000000000 : ℝ)*(sp3) + (745041449/12500000000000 : ℝ)*(sp4) + (2714921577/100000000000000 : ℝ)*(sp7) + (407740235245693/100000000000000 : ℝ)*(f.failure) + (43764801894569/5000000000000 : ℝ)*(f.sum) + (65361709955037/100000000000000000000000000000 : ℝ)*base66 + (778766337044963/200000000000000000000000000000 : ℝ)*base67 + (1554269279644963/200000000000000000000000000000 : ℝ)*base69 + (1022085264844963/200000000000000000000000000000 : ℝ)*base71 + (421582067255037/100000000000000000000000000000 : ℝ)*base74 + (829335692444963/200000000000000000000000000000 : ℝ)*base75 + (117541152644963/200000000000000000000000000000 : ℝ)*base77 + (512597444155037/200000000000000000000000000000 : ℝ)*base80 + (68404707155037/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (12245641/10000000000000000000000 : ℝ)*base89 + (12245641/10000000000000000000000 : ℝ)*base91 + (12245641/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (851905406753692475133129/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (358604513/20000000000000 : ℝ)*(base19) + (373572357/20000000000000 : ℝ)*(base23) + (223507717/100000000000000 : ℝ)*(base32) + (278392939/100000000000000 : ℝ)*(upper3) + (162539163/100000000000000 : ℝ)*(upper5) + (676817096234311/100000000000000 : ℝ)*(major0) + (676817096234311/100000000000000 : ℝ)*(major1) + (676817096234311/100000000000000 : ℝ)*(major2) + (1911059549/50000000000000 : ℝ)*(sp1) + (963505747/20000000000000 : ℝ)*(sp2) + (923458208834271/100000000000000 : ℝ)*(sp4) + (923452593692609/100000000000000 : ℝ)*(sp5) + (115431440430469/12500000000000 : ℝ)*(sp6) + (107543869039539/25000000000000 : ℝ)*(sp7) + (430175699665873/100000000000000 : ℝ)*(f.failure) + (923458208834271/100000000000000 : ℝ)*(f.sum) + (152588091411043/200000000000000000000000000000 : ℝ)*base66 + (3648642397188957/400000000000000000000000000000 : ℝ)*base67 + (2656483750388957/400000000000000000000000000000 : ℝ)*base69 + (253505797611043/400000000000000000000000000000 : ℝ)*base72 + (1155966403188957/200000000000000000000000000000 : ℝ)*base73 + (853145137611043/400000000000000000000000000000 : ℝ)*base76 + (14509955188957/400000000000000000000000000000 : ℝ)*base77 + (631700452388957/400000000000000000000000000000 : ℝ)*base79 + (435886876788957/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (83907699/10000000000000000000000 : ℝ)*base90 + (83907699/10000000000000000000000 : ℝ)*base92 + (83907699/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1408_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (949/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6601/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1408_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1408_s1_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-973052387/5000000000 : ℝ)*x 0 + (1122752567/2000000000 : ℝ)*x 1 + (5069169937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973052387/5000000000 : ℝ)^273 ≤ (11789479436509/100000000000000 : ℝ)^209 := by
    have hnat : (973052387 : ℕ)^273*100000000000000^209 ≤ 11789479436509^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973052387 5000000000 11789479436509 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122752567/2000000000 : ℝ)^273 ≤ (47040357709349/100000000000000 : ℝ)^209 := by
    have hnat : (1122752567 : ℕ)^273*100000000000000^209 ≤ 47040357709349^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122752567 2000000000 47040357709349 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069169937/10000000000 : ℝ)^273 ≤ (5146270354867/12500000000000 : ℝ)^209 := by
    have hnat : (5069169937 : ℕ)^273*12500000000000^209 ≤ 5146270354867^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069169937 10000000000 5146270354867 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-973052387/5000000000 : ℝ), (1122752567/2000000000 : ℝ), (5069169937/10000000000 : ℝ)] ![(11789479436509/100000000000000 : ℝ), (47040357709349/100000000000000 : ℝ), (5146270354867/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-973052387/5000000000 : ℝ)|^273 ≤ (11789479436509/100000000000000 : ℝ)^209
        have hw : |(-973052387/5000000000 : ℝ)|=(973052387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122752567/2000000000 : ℝ)|^273 ≤ (47040357709349/100000000000000 : ℝ)^209
        have hw : |(1122752567/2000000000 : ℝ)|=(1122752567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069169937/10000000000 : ℝ)|^273 ≤ (5146270354867/12500000000000 : ℝ)^209
        have hw : |(5069169937/10000000000 : ℝ)|=(5069169937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s1_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (215957173/400000000 : ℝ)*x 0 + (-2235146719/10000000000 : ℝ)*x 1 + (5069170509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215957173/400000000 : ℝ)^273 ≤ (44702814057103/100000000000000 : ℝ)^209 := by
    have hnat : (215957173 : ℕ)^273*100000000000000^209 ≤ 44702814057103^209*400000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215957173 400000000 44702814057103 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235146719/10000000000 : ℝ)^273 ≤ (7063508510467/50000000000000 : ℝ)^209 := by
    have hnat : (2235146719 : ℕ)^273*50000000000000^209 ≤ 7063508510467^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235146719 10000000000 7063508510467 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069170509/10000000000 : ℝ)^273 ≤ (5146271113389/12500000000000 : ℝ)^209 := by
    have hnat : (5069170509 : ℕ)^273*12500000000000^209 ≤ 5146271113389^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069170509 10000000000 5146271113389 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215957173/400000000 : ℝ), (-2235146719/10000000000 : ℝ), (5069170509/10000000000 : ℝ)] ![(44702814057103/100000000000000 : ℝ), (7063508510467/50000000000000 : ℝ), (5146271113389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215957173/400000000 : ℝ)|^273 ≤ (44702814057103/100000000000000 : ℝ)^209
        have hw : |(215957173/400000000 : ℝ)|=(215957173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235146719/10000000000 : ℝ)|^273 ≤ (7063508510467/50000000000000 : ℝ)^209
        have hw : |(-2235146719/10000000000 : ℝ)|=(2235146719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069170509/10000000000 : ℝ)|^273 ≤ (5146271113389/12500000000000 : ℝ)^209
        have hw : |(5069170509/10000000000 : ℝ)|=(5069170509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s1_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5398929833/10000000000 : ℝ)*x 0 + (2534585091/5000000000 : ℝ)*x 1 + (-1117573237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398929833/10000000000 : ℝ)^273 ≤ (22351409775669/50000000000000 : ℝ)^209 := by
    have hnat : (5398929833 : ℕ)^273*50000000000000^209 ≤ 22351409775669^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398929833 10000000000 22351409775669 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2534585091/5000000000 : ℝ)^273 ≤ (41170165438067/100000000000000 : ℝ)^209 := by
    have hnat : (2534585091 : ℕ)^273*100000000000000^209 ≤ 41170165438067^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534585091 5000000000 41170165438067 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117573237/5000000000 : ℝ)^273 ≤ (2825402999651/20000000000000 : ℝ)^209 := by
    have hnat : (1117573237 : ℕ)^273*20000000000000^209 ≤ 2825402999651^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117573237 5000000000 2825402999651 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398929833/10000000000 : ℝ), (2534585091/5000000000 : ℝ), (-1117573237/5000000000 : ℝ)] ![(22351409775669/50000000000000 : ℝ), (41170165438067/100000000000000 : ℝ), (2825402999651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398929833/10000000000 : ℝ)|^273 ≤ (22351409775669/50000000000000 : ℝ)^209
        have hw : |(5398929833/10000000000 : ℝ)|=(5398929833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2534585091/5000000000 : ℝ)|^273 ≤ (41170165438067/100000000000000 : ℝ)^209
        have hw : |(2534585091/5000000000 : ℝ)|=(2534585091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1117573237/5000000000 : ℝ)|^273 ≤ (2825402999651/20000000000000 : ℝ)^209
        have hw : |(-1117573237/5000000000 : ℝ)|=(1117573237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s1_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (428044719/1000000000 : ℝ)*x 0 + (746371391/2000000000 : ℝ)*x 1 + (2450467039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428044719/1000000000 : ℝ)^273 ≤ (2063116397699/6250000000000 : ℝ)^209 := by
    have hnat : (428044719 : ℕ)^273*6250000000000^209 ≤ 2063116397699^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428044719 1000000000 2063116397699 6250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746371391/2000000000 : ℝ)^273 ≤ (27595598499193/100000000000000 : ℝ)^209 := by
    have hnat : (746371391 : ℕ)^273*100000000000000^209 ≤ 27595598499193^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746371391 2000000000 27595598499193 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2450467039/5000000000 : ℝ)^273 ≤ (19697269562093/50000000000000 : ℝ)^209 := by
    have hnat : (2450467039 : ℕ)^273*50000000000000^209 ≤ 19697269562093^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2450467039 5000000000 19697269562093 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428044719/1000000000 : ℝ), (746371391/2000000000 : ℝ), (2450467039/5000000000 : ℝ)] ![(2063116397699/6250000000000 : ℝ), (27595598499193/100000000000000 : ℝ), (19697269562093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428044719/1000000000 : ℝ)|^273 ≤ (2063116397699/6250000000000 : ℝ)^209
        have hw : |(428044719/1000000000 : ℝ)|=(428044719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746371391/2000000000 : ℝ)|^273 ≤ (27595598499193/100000000000000 : ℝ)^209
        have hw : |(746371391/2000000000 : ℝ)|=(746371391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2450467039/5000000000 : ℝ)|^273 ≤ (19697269562093/50000000000000 : ℝ)^209
        have hw : |(2450467039/5000000000 : ℝ)|=(2450467039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s1_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1946532517/10000000000 : ℝ)*x 0 + (5075661821/10000000000 : ℝ)*x 1 + (5607158999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946532517/10000000000 : ℝ)^273 ≤ (2948216077219/25000000000000 : ℝ)^209 := by
    have hnat : (1946532517 : ℕ)^273*25000000000000^209 ≤ 2948216077219^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946532517 10000000000 2948216077219 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075661821/10000000000 : ℝ)^273 ≤ (41239046777367/100000000000000 : ℝ)^209 := by
    have hnat : (5075661821 : ℕ)^273*100000000000000^209 ≤ 41239046777367^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075661821 10000000000 41239046777367 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5607158999/10000000000 : ℝ)^273 ≤ (23484044446279/50000000000000 : ℝ)^209 := by
    have hnat : (5607158999 : ℕ)^273*50000000000000^209 ≤ 23484044446279^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607158999 10000000000 23484044446279 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1946532517/10000000000 : ℝ), (5075661821/10000000000 : ℝ), (5607158999/10000000000 : ℝ)] ![(2948216077219/25000000000000 : ℝ), (41239046777367/100000000000000 : ℝ), (23484044446279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1946532517/10000000000 : ℝ)|^273 ≤ (2948216077219/25000000000000 : ℝ)^209
        have hw : |(-1946532517/10000000000 : ℝ)|=(1946532517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075661821/10000000000 : ℝ)|^273 ≤ (41239046777367/100000000000000 : ℝ)^209
        have hw : |(5075661821/10000000000 : ℝ)|=(5075661821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5607158999/10000000000 : ℝ)|^273 ≤ (23484044446279/50000000000000 : ℝ)^209
        have hw : |(5607158999/10000000000 : ℝ)|=(5607158999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s1_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5256866479/10000000000 : ℝ)*x 0 + (-212144789/1250000000 : ℝ)*x 1 + (2803579427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256866479/10000000000 : ℝ)^273 ≤ (43172572267349/100000000000000 : ℝ)^209 := by
    have hnat : (5256866479 : ℕ)^273*100000000000000^209 ≤ 43172572267349^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256866479 10000000000 43172572267349 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212144789/1250000000 : ℝ)^273 ≤ (9859340406503/100000000000000 : ℝ)^209 := by
    have hnat : (212144789 : ℕ)^273*100000000000000^209 ≤ 9859340406503^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212144789 1250000000 9859340406503 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2803579427/5000000000 : ℝ)^273 ≤ (46968087306043/100000000000000 : ℝ)^209 := by
    have hnat : (2803579427 : ℕ)^273*100000000000000^209 ≤ 46968087306043^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803579427 5000000000 46968087306043 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256866479/10000000000 : ℝ), (-212144789/1250000000 : ℝ), (2803579427/5000000000 : ℝ)] ![(43172572267349/100000000000000 : ℝ), (9859340406503/100000000000000 : ℝ), (46968087306043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256866479/10000000000 : ℝ)|^273 ≤ (43172572267349/100000000000000 : ℝ)^209
        have hw : |(5256866479/10000000000 : ℝ)|=(5256866479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212144789/1250000000 : ℝ)|^273 ≤ (9859340406503/100000000000000 : ℝ)^209
        have hw : |(-212144789/1250000000 : ℝ)|=(212144789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2803579427/5000000000 : ℝ)|^273 ≤ (46968087306043/100000000000000 : ℝ)^209
        have hw : |(2803579427/5000000000 : ℝ)|=(2803579427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s1_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (657108387/1250000000 : ℝ)*x 0 + (5607159343/10000000000 : ℝ)*x 1 + (-339431347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657108387/1250000000 : ℝ)^273 ≤ (21586289443099/50000000000000 : ℝ)^209 := by
    have hnat : (657108387 : ℕ)^273*50000000000000^209 ≤ 21586289443099^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657108387 1250000000 21586289443099 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607159343/10000000000 : ℝ)^273 ≤ (4696809265643/10000000000000 : ℝ)^209 := by
    have hnat : (5607159343 : ℕ)^273*10000000000000^209 ≤ 4696809265643^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607159343 10000000000 4696809265643 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339431347/2000000000 : ℝ)^273 ≤ (2464832109957/25000000000000 : ℝ)^209 := by
    have hnat : (339431347 : ℕ)^273*25000000000000^209 ≤ 2464832109957^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339431347 2000000000 2464832109957 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657108387/1250000000 : ℝ), (5607159343/10000000000 : ℝ), (-339431347/2000000000 : ℝ)] ![(21586289443099/50000000000000 : ℝ), (4696809265643/10000000000000 : ℝ), (2464832109957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657108387/1250000000 : ℝ)|^273 ≤ (21586289443099/50000000000000 : ℝ)^209
        have hw : |(657108387/1250000000 : ℝ)|=(657108387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5607159343/10000000000 : ℝ)|^273 ≤ (4696809265643/10000000000000 : ℝ)^209
        have hw : |(5607159343/10000000000 : ℝ)|=(5607159343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339431347/2000000000 : ℝ)|^273 ≤ (2464832109957/25000000000000 : ℝ)^209
        have hw : |(-339431347/2000000000 : ℝ)|=(339431347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s1_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1070341731/2500000000 : ℝ)*x 0 + (4886996697/10000000000 : ℝ)*x 1 + (3746033279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070341731/2500000000 : ℝ)^273 ≤ (33019127406611/100000000000000 : ℝ)^209 := by
    have hnat : (1070341731 : ℕ)^273*100000000000000^209 ≤ 33019127406611^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070341731 2500000000 33019127406611 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4886996697/10000000000 : ℝ)^273 ≤ (9812066424743/25000000000000 : ℝ)^209 := by
    have hnat : (4886996697 : ℕ)^273*25000000000000^209 ≤ 9812066424743^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886996697 10000000000 9812066424743 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3746033279/10000000000 : ℝ)^273 ≤ (27732606876181/100000000000000 : ℝ)^209 := by
    have hnat : (3746033279 : ℕ)^273*100000000000000^209 ≤ 27732606876181^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746033279 10000000000 27732606876181 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070341731/2500000000 : ℝ), (4886996697/10000000000 : ℝ), (3746033279/10000000000 : ℝ)] ![(33019127406611/100000000000000 : ℝ), (9812066424743/25000000000000 : ℝ), (27732606876181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070341731/2500000000 : ℝ)|^273 ≤ (33019127406611/100000000000000 : ℝ)^209
        have hw : |(1070341731/2500000000 : ℝ)|=(1070341731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4886996697/10000000000 : ℝ)|^273 ≤ (9812066424743/25000000000000 : ℝ)^209
        have hw : |(4886996697/10000000000 : ℝ)|=(4886996697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3746033279/10000000000 : ℝ)|^273 ≤ (27732606876181/100000000000000 : ℝ)^209
        have hw : |(3746033279/10000000000 : ℝ)|=(3746033279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6601/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (949/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1869/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4747/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6601/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (949/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6601/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (949/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6601/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (949/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6601/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (949/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6601/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (949/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6601/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (949/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (949/50000 : ℝ) ^ (4367/1024 : ℝ) ≤ (4545049463649/100000000000000000000 : ℝ) := by
    have hpowers : (949/50000 : ℝ)^4367 ≤ (4545049463649/100000000000000000000 : ℝ)^1024 := by
      have hnat : (949 : ℕ)^4367*100000000000000000000^1024 ≤ 4545049463649^1024*50000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        949 50000 4545049463649 100000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (949/50000 : ℝ)) (X := (4545049463649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6601/25000 : ℝ) ^ (4367/1024 : ℝ) ≤ (85421009799661739/25000000000000000000 : ℝ) := by
    have hpowers : (6601/25000 : ℝ)^4367 ≤ (85421009799661739/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6601 : ℕ)^4367*25000000000000000000^1024 ≤ 85421009799661739^1024*25000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6601 25000 85421009799661739 25000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6601/25000 : ℝ)) (X := (85421009799661739/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000004545049463649/50000000000000000000 : ℝ) ≤ (10000000213150011/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (50000004545049463649/50000000000000000000 : ℝ)^1024 ≤ (10000000213150011/10000000000000000 : ℝ)^4367 := by
      have hnat : (50000004545049463649 : ℕ)^1024*10000000000000000^4367 ≤ 10000000213150011^4367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004545049463649 50000000000000000000 10000000213150011 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000213150011/10000000000000000 : ℝ)) (X := (50000004545049463649/50000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20068337716849622121/20000000000000000000 : ℝ) ≤ (10008001658582537/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (20068337716849622121/20000000000000000000 : ℝ)^1024 ≤ (10008001658582537/10000000000000000 : ℝ)^4367 := by
      have hnat : (20068337716849622121 : ℕ)^1024*10000000000000000^4367 ≤ 10008001658582537^4367*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20068337716849622121 20000000000000000000 10008001658582537 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008001658582537/10000000000000000 : ℝ)) (X := (20068337716849622121/20000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12585421009799661739/12500000000000000000 : ℝ) ≤ (10016003104015063/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (12585421009799661739/12500000000000000000 : ℝ)^1024 ≤ (10016003104015063/10000000000000000 : ℝ)^4367 := by
      have hnat : (12585421009799661739 : ℕ)^1024*10000000000000000^4367 ≤ 10016003104015063^4367*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12585421009799661739 12500000000000000000 10016003104015063 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016003104015063/10000000000000000 : ℝ)) (X := (12585421009799661739/12500000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4545049463649/100000000000000000000 : ℝ) ≤ ((24502963173659230087/24506000000000000000 : ℝ)+2*(4000722716263/1225300000000000 : ℝ)*(949/50000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (24502963173659230087/24506000000000000000 : ℝ)+2*(4000722716263/1225300000000000 : ℝ)*(949/50000 : ℝ)=(10000000213150011/10000000000000000 : ℝ) by norm_num, show 1+2*(4545049463649/100000000000000000000 : ℝ)=(50000004545049463649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(85421009799661739/25000000000000000000 : ℝ)+(4545049463649/100000000000000000000 : ℝ) ≤ ((24502963173659230087/24506000000000000000 : ℝ)+(4000722716263/1225300000000000 : ℝ)*((6601/25000 : ℝ)+(949/50000 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (24502963173659230087/24506000000000000000 : ℝ)+(4000722716263/1225300000000000 : ℝ)*((6601/25000 : ℝ)+(949/50000 : ℝ))=(10008001658582537/10000000000000000 : ℝ) by norm_num, show 1+(85421009799661739/25000000000000000000 : ℝ)+(4545049463649/100000000000000000000 : ℝ)=(20068337716849622121/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(85421009799661739/25000000000000000000 : ℝ) ≤ ((24502963173659230087/24506000000000000000 : ℝ)+2*(4000722716263/1225300000000000 : ℝ)*(6601/25000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (24502963173659230087/24506000000000000000 : ℝ)+2*(4000722716263/1225300000000000 : ℝ)*(6601/25000 : ℝ)=(10016003104015063/10000000000000000 : ℝ) by norm_num, show 1+2*(85421009799661739/25000000000000000000 : ℝ)=(12585421009799661739/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24502963173659230087/24506000000000000000 : ℝ)*(X 1 0+X 2 0)+(4000722716263/1225300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (949/50000 : ℝ)) (hi := (6601/25000 : ℝ)) (c := (24502963173659230087/24506000000000000000 : ℝ)) (alpha := (4000722716263/1225300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24502963173659230087/24506000000000000000 : ℝ)*(X 0 1+X 2 1)+(4000722716263/1225300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (949/50000 : ℝ)) (hi := (6601/25000 : ℝ)) (c := (24502963173659230087/24506000000000000000 : ℝ)) (alpha := (4000722716263/1225300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24502963173659230087/24506000000000000000 : ℝ)*(X 0 2+X 1 2)+(4000722716263/1225300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (949/50000 : ℝ)) (hi := (6601/25000 : ℝ)) (c := (24502963173659230087/24506000000000000000 : ℝ)) (alpha := (4000722716263/1225300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-973052387/5000000000 : ℝ)*X 0 0+(1122752567/2000000000 : ℝ)*X 0 1+(5069169937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((215957173/400000000 : ℝ)*X 1 0+(-2235146719/10000000000 : ℝ)*X 1 1+(5069170509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5398929833/10000000000 : ℝ)*X 2 0+(2534585091/5000000000 : ℝ)*X 2 1+(-1117573237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((428044719/1000000000 : ℝ)*X 0 0+(746371391/2000000000 : ℝ)*X 0 1+(2450467039/5000000000 : ℝ)*X 0 2+(428044719/1000000000 : ℝ)*X 1 0+(746371391/2000000000 : ℝ)*X 1 1+(2450467039/5000000000 : ℝ)*X 1 2+(428044719/1000000000 : ℝ)*X 2 0+(746371391/2000000000 : ℝ)*X 2 1+(2450467039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1946532517/10000000000 : ℝ)*X 0 0+(5075661821/10000000000 : ℝ)*X 0 1+(5607158999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256866479/10000000000 : ℝ)*X 1 0+(-212144789/1250000000 : ℝ)*X 1 1+(2803579427/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657108387/1250000000 : ℝ)*X 2 0+(5607159343/10000000000 : ℝ)*X 2 1+(-339431347/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070341731/2500000000 : ℝ)*X 0 0+(4886996697/10000000000 : ℝ)*X 0 1+(3746033279/10000000000 : ℝ)*X 0 2+(1070341731/2500000000 : ℝ)*X 1 0+(4886996697/10000000000 : ℝ)*X 1 1+(3746033279/10000000000 : ℝ)*X 1 2+(1070341731/2500000000 : ℝ)*X 2 0+(4886996697/10000000000 : ℝ)*X 2 1+(3746033279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (345195633616384979064132333/61265000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3332487/10000000000000 : ℝ)*(base1) + (524184497/50000000000000 : ℝ)*(base19) + (1221146817/100000000000000 : ℝ)*(base23) + (15155753/25000000000000 : ℝ)*(upper3) + (208395883/100000000000000 : ℝ)*(upper5) + (134581759116447/10000000000000 : ℝ)*(major0) + (134581759116447/10000000000000 : ℝ)*(major1) + (134581759116447/10000000000000 : ℝ)*(major2) + (91812081670041/5000000000000 : ℝ)*(sp0) + (114765666988177/6250000000000 : ℝ)*(sp1) + (114765656189563/6250000000000 : ℝ)*(sp2) + (427689816034427/50000000000000 : ℝ)*(sp3) + (10120103877/100000000000000 : ℝ)*(sp4) + (902234951/25000000000000 : ℝ)*(sp7) + (855383274333529/100000000000000 : ℝ)*(f.failure) + (918125860089913/50000000000000 : ℝ)*(f.sum) + (27979771494171/12253000000000000000000000000 : ℝ)*base65 + (1428653593874660889/245060000000000000000000000000000 : ℝ)*base67 + (333014059728299111/245060000000000000000000000000000 : ℝ)*base70 + (573492247036800889/245060000000000000000000000000000 : ℝ)*base71 + (16682573056843/3063250000000000000000000000 : ℝ)*base73 + (1958133724185200889/245060000000000000000000000000000 : ℝ)*base75 + (2336581498600960889/245060000000000000000000000000000 : ℝ)*base77 + (3151459031055320889/245060000000000000000000000000000 : ℝ)*base79 + (21386057300643/6126500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (64444427/10000000000000000000000 : ℝ)*base90 + (64444427/10000000000000000000000 : ℝ)*base92 + (64444427/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1001830439242947263213209017/306325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21902621/10000000000000 : ℝ)*(base1) + (971381379/100000000000000 : ℝ)*(base19) + (656127473/50000000000000 : ℝ)*(base23) + (3346409/6250000000000 : ℝ)*(upper3) + (107173521/50000000000000 : ℝ)*(upper5) + (689483127518203/50000000000000 : ℝ)*(major0) + (689483127518203/50000000000000 : ℝ)*(major1) + (689483127518203/50000000000000 : ℝ)*(major2) + (4146501031/100000000000000 : ℝ)*(sp1) + (429429301/5000000000000 : ℝ)*(sp2) + (1881480507870707/100000000000000 : ℝ)*(sp4) + (235184396370261/12500000000000 : ℝ)*(sp5) + (1881470388003531/100000000000000 : ℝ)*(sp6) + (219112973296507/25000000000000 : ℝ)*(sp7) + (438226056106119/50000000000000 : ℝ)*(f.failure) + (1881480288844497/100000000000000 : ℝ)*(f.sum) + (44133563725767/61265000000000000000000000000 : ℝ)*base66 + (13329762441001653661/1225300000000000000000000000000000 : ℝ)*base67 + (1538160009709053661/1225300000000000000000000000000000 : ℝ)*base69 + (3203033941460853661/1225300000000000000000000000000000 : ℝ)*base71 + (168097682945463/61265000000000000000000000000 : ℝ)*base73 + (1190925730732346339/1225300000000000000000000000000000 : ℝ)*base76 + (9433968209913153661/1225300000000000000000000000000000 : ℝ)*base77 + (19988632836153853661/1225300000000000000000000000000000 : ℝ)*base79 + (257693716373677/61265000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8791403/5000000000000000000000 : ℝ)*base89 + (8791403/5000000000000000000000 : ℝ)*base91 + (8791403/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1408_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6601/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (949/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1869/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4747/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1408_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1408_s2_0 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980834157/10000000000 : ℝ)*x 0 + (5462992789/10000000000 : ℝ)*x 1 + (1039522257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980834157/10000000000 : ℝ)^273 ≤ (120650431407/1000000000000 : ℝ)^209 := by
    have hnat : (1980834157 : ℕ)^273*1000000000000^209 ≤ 120650431407^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980834157 10000000000 120650431407 1000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462992789/10000000000 : ℝ)^273 ≤ (11349235751863/25000000000000 : ℝ)^209 := by
    have hnat : (5462992789 : ℕ)^273*25000000000000^209 ≤ 11349235751863^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462992789 10000000000 11349235751863 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039522257/2000000000 : ℝ)^273 ≤ (42538013830703/100000000000000 : ℝ)^209 := by
    have hnat : (1039522257 : ℕ)^273*100000000000000^209 ≤ 42538013830703^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039522257 2000000000 42538013830703 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980834157/10000000000 : ℝ), (5462992789/10000000000 : ℝ), (1039522257/2000000000 : ℝ)] ![(120650431407/1000000000000 : ℝ), (11349235751863/25000000000000 : ℝ), (42538013830703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980834157/10000000000 : ℝ)|^273 ≤ (120650431407/1000000000000 : ℝ)^209
        have hw : |(-1980834157/10000000000 : ℝ)|=(1980834157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462992789/10000000000 : ℝ)|^273 ≤ (11349235751863/25000000000000 : ℝ)^209
        have hw : |(5462992789/10000000000 : ℝ)|=(5462992789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039522257/2000000000 : ℝ)|^273 ≤ (42538013830703/100000000000000 : ℝ)^209
        have hw : |(1039522257/2000000000 : ℝ)|=(1039522257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s2_1 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5361488209/10000000000 : ℝ)*x 0 + (-16542981/78125000 : ℝ)*x 1 + (5197611267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361488209/10000000000 : ℝ)^273 ≤ (885966062873/2000000000000 : ℝ)^209 := by
    have hnat : (5361488209 : ℕ)^273*2000000000000^209 ≤ 885966062873^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361488209 10000000000 885966062873 2000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16542981/78125000 : ℝ)^273 ≤ (658184160003/5000000000000 : ℝ)^209 := by
    have hnat : (16542981 : ℕ)^273*5000000000000^209 ≤ 658184160003^209*78125000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16542981 78125000 658184160003 5000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5197611267/10000000000 : ℝ)^273 ≤ (21269006819139/50000000000000 : ℝ)^209 := by
    have hnat : (5197611267 : ℕ)^273*50000000000000^209 ≤ 21269006819139^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197611267 10000000000 21269006819139 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361488209/10000000000 : ℝ), (-16542981/78125000 : ℝ), (5197611267/10000000000 : ℝ)] ![(885966062873/2000000000000 : ℝ), (658184160003/5000000000000 : ℝ), (21269006819139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361488209/10000000000 : ℝ)|^273 ≤ (885966062873/2000000000000 : ℝ)^209
        have hw : |(5361488209/10000000000 : ℝ)|=(5361488209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16542981/78125000 : ℝ)|^273 ≤ (658184160003/5000000000000 : ℝ)^209
        have hw : |(-16542981/78125000 : ℝ)|=(16542981/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5197611267/10000000000 : ℝ)|^273 ≤ (21269006819139/50000000000000 : ℝ)^209
        have hw : |(5197611267/10000000000 : ℝ)|=(5197611267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s2_2 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1340371993/2500000000 : ℝ)*x 0 + (1039522307/2000000000 : ℝ)*x 1 + (-211750153/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340371993/2500000000 : ℝ)^273 ≤ (885966011717/2000000000000 : ℝ)^209 := by
    have hnat : (1340371993 : ℕ)^273*2000000000000^209 ≤ 885966011717^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340371993 2500000000 885966011717 2000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039522307/2000000000 : ℝ)^273 ≤ (42538016503277/100000000000000 : ℝ)^209 := by
    have hnat : (1039522307 : ℕ)^273*100000000000000^209 ≤ 42538016503277^209*2000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039522307 2000000000 42538016503277 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211750153/1000000000 : ℝ)^273 ≤ (1316368289149/10000000000000 : ℝ)^209 := by
    have hnat : (211750153 : ℕ)^273*10000000000000^209 ≤ 1316368289149^209*1000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211750153 1000000000 1316368289149 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340371993/2500000000 : ℝ), (1039522307/2000000000 : ℝ), (-211750153/1000000000 : ℝ)] ![(885966011717/2000000000000 : ℝ), (42538016503277/100000000000000 : ℝ), (1316368289149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340371993/2500000000 : ℝ)|^273 ≤ (885966011717/2000000000000 : ℝ)^209
        have hw : |(1340371993/2500000000 : ℝ)|=(1340371993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039522307/2000000000 : ℝ)|^273 ≤ (42538016503277/100000000000000 : ℝ)^209
        have hw : |(1039522307/2000000000 : ℝ)|=(1039522307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211750153/1000000000 : ℝ)|^273 ≤ (1316368289149/10000000000000 : ℝ)^209
        have hw : |(-211750153/1000000000 : ℝ)|=(211750153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s2_3 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (269056861/625000000 : ℝ)*x 0 + (4028598579/10000000000 : ℝ)*x 1 + (1149573309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269056861/625000000 : ℝ)^273 ≤ (6651299238419/20000000000000 : ℝ)^209 := by
    have hnat : (269056861 : ℕ)^273*20000000000000^209 ≤ 6651299238419^209*625000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269056861 625000000 6651299238419 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028598579/10000000000 : ℝ)^273 ≤ (3049609373489/10000000000000 : ℝ)^209 := by
    have hnat : (4028598579 : ℕ)^273*10000000000000^209 ≤ 3049609373489^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028598579 10000000000 3049609373489 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149573309/2500000000 : ℝ)^273 ≤ (4530926257377/12500000000000 : ℝ)^209 := by
    have hnat : (1149573309 : ℕ)^273*12500000000000^209 ≤ 4530926257377^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149573309 2500000000 4530926257377 12500000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269056861/625000000 : ℝ), (4028598579/10000000000 : ℝ), (1149573309/2500000000 : ℝ)] ![(6651299238419/20000000000000 : ℝ), (3049609373489/10000000000000 : ℝ), (4530926257377/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269056861/625000000 : ℝ)|^273 ≤ (6651299238419/20000000000000 : ℝ)^209
        have hw : |(269056861/625000000 : ℝ)|=(269056861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028598579/10000000000 : ℝ)|^273 ≤ (3049609373489/10000000000000 : ℝ)^209
        have hw : |(4028598579/10000000000 : ℝ)|=(4028598579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1149573309/2500000000 : ℝ)|^273 ≤ (4530926257377/12500000000000 : ℝ)^209
        have hw : |(1149573309/2500000000 : ℝ)|=(1149573309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s2_4 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1980883489/10000000000 : ℝ)*x 0 + (5199162399/10000000000 : ℝ)*x 1 + (1365357213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1980883489/10000000000 : ℝ)^273 ≤ (754089726857/6250000000000 : ℝ)^209 := by
    have hnat : (1980883489 : ℕ)^273*6250000000000^209 ≤ 754089726857^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980883489 10000000000 754089726857 6250000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5199162399/10000000000 : ℝ)^273 ≤ (42554596457707/100000000000000 : ℝ)^209 := by
    have hnat : (5199162399 : ℕ)^273*100000000000000^209 ≤ 42554596457707^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199162399 10000000000 42554596457707 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365357213/2500000000 : ℝ)^273 ≤ (45379967898939/100000000000000 : ℝ)^209 := by
    have hnat : (1365357213 : ℕ)^273*100000000000000^209 ≤ 45379967898939^209*2500000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365357213 2500000000 45379967898939 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1980883489/10000000000 : ℝ), (5199162399/10000000000 : ℝ), (1365357213/2500000000 : ℝ)] ![(754089726857/6250000000000 : ℝ), (42554596457707/100000000000000 : ℝ), (45379967898939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1980883489/10000000000 : ℝ)|^273 ≤ (754089726857/6250000000000 : ℝ)^209
        have hw : |(-1980883489/10000000000 : ℝ)|=(1980883489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5199162399/10000000000 : ℝ)|^273 ≤ (42554596457707/100000000000000 : ℝ)^209
        have hw : |(5199162399/10000000000 : ℝ)|=(5199162399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365357213/2500000000 : ℝ)|^273 ≤ (45379967898939/100000000000000 : ℝ)^209
        have hw : |(1365357213/2500000000 : ℝ)|=(1365357213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s2_5 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5292619023/10000000000 : ℝ)*x 0 + (-926842299/5000000000 : ℝ)*x 1 + (5461428573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292619023/10000000000 : ℝ)^273 ≤ (4355650539313/10000000000000 : ℝ)^209 := by
    have hnat : (5292619023 : ℕ)^273*10000000000000^209 ≤ 4355650539313^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292619023 10000000000 4355650539313 10000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (926842299/5000000000 : ℝ)^273 ≤ (5531764859329/50000000000000 : ℝ)^209 := by
    have hnat : (926842299 : ℕ)^273*50000000000000^209 ≤ 5531764859329^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926842299 5000000000 5531764859329 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461428573/10000000000 : ℝ)^273 ≤ (22689982435391/50000000000000 : ℝ)^209 := by
    have hnat : (5461428573 : ℕ)^273*50000000000000^209 ≤ 22689982435391^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461428573 10000000000 22689982435391 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292619023/10000000000 : ℝ), (-926842299/5000000000 : ℝ), (5461428573/10000000000 : ℝ)] ![(4355650539313/10000000000000 : ℝ), (5531764859329/50000000000000 : ℝ), (22689982435391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292619023/10000000000 : ℝ)|^273 ≤ (4355650539313/10000000000000 : ℝ)^209
        have hw : |(5292619023/10000000000 : ℝ)|=(5292619023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-926842299/5000000000 : ℝ)|^273 ≤ (5531764859329/50000000000000 : ℝ)^209
        have hw : |(-926842299/5000000000 : ℝ)|=(926842299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461428573/10000000000 : ℝ)|^273 ≤ (22689982435391/50000000000000 : ℝ)^209
        have hw : |(5461428573/10000000000 : ℝ)|=(5461428573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s2_6 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5292620451/10000000000 : ℝ)*x 0 + (5461428549/10000000000 : ℝ)*x 1 + (-1853682663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292620451/10000000000 : ℝ)^273 ≤ (10889130185947/25000000000000 : ℝ)^209 := by
    have hnat : (5292620451 : ℕ)^273*25000000000000^209 ≤ 10889130185947^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292620451 10000000000 10889130185947 25000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461428549/10000000000 : ℝ)^273 ≤ (9075992922059/20000000000000 : ℝ)^209 := by
    have hnat : (5461428549 : ℕ)^273*20000000000000^209 ≤ 9075992922059^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461428549 10000000000 9075992922059 20000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1853682663/10000000000 : ℝ)^273 ≤ (11063514633317/100000000000000 : ℝ)^209 := by
    have hnat : (1853682663 : ℕ)^273*100000000000000^209 ≤ 11063514633317^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853682663 10000000000 11063514633317 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292620451/10000000000 : ℝ), (5461428549/10000000000 : ℝ), (-1853682663/10000000000 : ℝ)] ![(10889130185947/25000000000000 : ℝ), (9075992922059/20000000000000 : ℝ), (11063514633317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292620451/10000000000 : ℝ)|^273 ≤ (10889130185947/25000000000000 : ℝ)^209
        have hw : |(5292620451/10000000000 : ℝ)|=(5292620451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461428549/10000000000 : ℝ)|^273 ≤ (9075992922059/20000000000000 : ℝ)^209
        have hw : |(5461428549/10000000000 : ℝ)|=(5461428549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1853682663/10000000000 : ℝ)|^273 ≤ (11063514633317/100000000000000 : ℝ)^209
        have hw : |(-1853682663/10000000000 : ℝ)|=(1853682663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1408_s2_7 (p : ℝ) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4305016869/10000000000 : ℝ)*x 0 + (574370489/1250000000 : ℝ)*x 1 + (2015977707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305016869/10000000000 : ℝ)^273 ≤ (16628788429109/50000000000000 : ℝ)^209 := by
    have hnat : (4305016869 : ℕ)^273*50000000000000^209 ≤ 16628788429109^209*10000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305016869 10000000000 16628788429109 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574370489/1250000000 : ℝ)^273 ≤ (36213132918491/100000000000000 : ℝ)^209 := by
    have hnat : (574370489 : ℕ)^273*100000000000000^209 ≤ 36213132918491^209*1250000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574370489 1250000000 36213132918491 100000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015977707/5000000000 : ℝ)^273 ≤ (15264645104823/50000000000000 : ℝ)^209 := by
    have hnat : (2015977707 : ℕ)^273*50000000000000^209 ≤ 15264645104823^209*5000000000^273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015977707 5000000000 15264645104823 50000000000000 273 209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (273/64 : ℝ)) 273 209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305016869/10000000000 : ℝ), (574370489/1250000000 : ℝ), (2015977707/5000000000 : ℝ)] ![(16628788429109/50000000000000 : ℝ), (36213132918491/100000000000000 : ℝ), (15264645104823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305016869/10000000000 : ℝ)|^273 ≤ (16628788429109/50000000000000 : ℝ)^209
        have hw : |(4305016869/10000000000 : ℝ)|=(4305016869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574370489/1250000000 : ℝ)|^273 ≤ (36213132918491/100000000000000 : ℝ)^209
        have hw : |(574370489/1250000000 : ℝ)|=(574370489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015977707/5000000000 : ℝ)|^273 ≤ (15264645104823/50000000000000 : ℝ)^209
        have hw : |(2015977707/5000000000 : ℝ)|=(2015977707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1408_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4747/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2563/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7933/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4747/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1869/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4747/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1869/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4747/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1869/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4747/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1869/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4747/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1869/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4747/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1869/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1869/25000 : ℝ) ^ (4367/1024 : ℝ) ≤ (3071323396197/195312500000000000 : ℝ) := by
    have hpowers : (1869/25000 : ℝ)^4367 ≤ (3071323396197/195312500000000000 : ℝ)^1024 := by
      have hnat : (1869 : ℕ)^4367*195312500000000000^1024 ≤ 3071323396197^1024*25000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1869 25000 3071323396197 195312500000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1869/25000 : ℝ)) (X := (3071323396197/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4747/25000 : ℝ) ^ (4367/1024 : ℝ) ≤ (83746669738189451/100000000000000000000 : ℝ) := by
    have hpowers : (4747/25000 : ℝ)^4367 ≤ (83746669738189451/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4747 : ℕ)^4367*100000000000000000000^1024 ≤ 83746669738189451^1024*25000^4367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4747 25000 83746669738189451 100000000000000000000 4367 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4747/25000 : ℝ)) (X := (83746669738189451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (97659321323396197/97656250000000000 : ℝ) ≤ (2000014749151519/2000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (97659321323396197/97656250000000000 : ℝ)^1024 ≤ (2000014749151519/2000000000000000 : ℝ)^4367 := by
      have hnat : (97659321323396197 : ℕ)^1024*2000000000000000^4367 ≤ 2000014749151519^4367*97656250000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97659321323396197 97656250000000000 2000014749151519 2000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000014749151519/2000000000000000 : ℝ)) (X := (97659321323396197/97656250000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20017063837463408463/20000000000000000000 : ℝ) ≤ (10001999961785161/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (20017063837463408463/20000000000000000000 : ℝ)^1024 ≤ (10001999961785161/10000000000000000 : ℝ)^4367 := by
      have hnat : (20017063837463408463 : ℕ)^1024*10000000000000000^4367 ≤ 10001999961785161^4367*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20017063837463408463 20000000000000000000 10001999961785161 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001999961785161/10000000000000000 : ℝ)) (X := (20017063837463408463/20000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50083746669738189451/50000000000000000000 : ℝ) ≤ (10003926177812727/10000000000000000 : ℝ) ^ (4367/1024 : ℝ) := by
    have hpowers : (50083746669738189451/50000000000000000000 : ℝ)^1024 ≤ (10003926177812727/10000000000000000 : ℝ)^4367 := by
      have hnat : (50083746669738189451 : ℕ)^1024*10000000000000000^4367 ≤ 10003926177812727^4367*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50083746669738189451 50000000000000000000 10003926177812727 10000000000000000 1024 4367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003926177812727/10000000000000000 : ℝ)) (X := (50083746669738189451/50000000000000000000 : ℝ)) (by norm_num) 4367 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3071323396197/195312500000000000 : ℝ) ≤ ((14386506022389658351/14390000000000000000 : ℝ)+2*(963108013783/575600000000000 : ℝ)*(1869/25000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (14386506022389658351/14390000000000000000 : ℝ)+2*(963108013783/575600000000000 : ℝ)*(1869/25000 : ℝ)=(2000014749151519/2000000000000000 : ℝ) by norm_num, show 1+2*(3071323396197/195312500000000000 : ℝ)=(97659321323396197/97656250000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(83746669738189451/100000000000000000000 : ℝ)+(3071323396197/195312500000000000 : ℝ) ≤ ((14386506022389658351/14390000000000000000 : ℝ)+(963108013783/575600000000000 : ℝ)*((4747/25000 : ℝ)+(1869/25000 : ℝ)))^(4367/1024 : ℝ) := by
    rw [show (14386506022389658351/14390000000000000000 : ℝ)+(963108013783/575600000000000 : ℝ)*((4747/25000 : ℝ)+(1869/25000 : ℝ))=(10001999961785161/10000000000000000 : ℝ) by norm_num, show 1+(83746669738189451/100000000000000000000 : ℝ)+(3071323396197/195312500000000000 : ℝ)=(20017063837463408463/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(83746669738189451/100000000000000000000 : ℝ) ≤ ((14386506022389658351/14390000000000000000 : ℝ)+2*(963108013783/575600000000000 : ℝ)*(4747/25000 : ℝ))^(4367/1024 : ℝ) := by
    rw [show (14386506022389658351/14390000000000000000 : ℝ)+2*(963108013783/575600000000000 : ℝ)*(4747/25000 : ℝ)=(10003926177812727/10000000000000000 : ℝ) by norm_num, show 1+2*(83746669738189451/100000000000000000000 : ℝ)=(50083746669738189451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14386506022389658351/14390000000000000000 : ℝ)*(X 1 0+X 2 0)+(963108013783/575600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (1869/25000 : ℝ)) (hi := (4747/25000 : ℝ)) (c := (14386506022389658351/14390000000000000000 : ℝ)) (alpha := (963108013783/575600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14386506022389658351/14390000000000000000 : ℝ)*(X 0 1+X 2 1)+(963108013783/575600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (1869/25000 : ℝ)) (hi := (4747/25000 : ℝ)) (c := (14386506022389658351/14390000000000000000 : ℝ)) (alpha := (963108013783/575600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14386506022389658351/14390000000000000000 : ℝ)*(X 0 2+X 1 2)+(963108013783/575600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4367/1024 : ℝ)) (lo := (1869/25000 : ℝ)) (hi := (4747/25000 : ℝ)) (c := (14386506022389658351/14390000000000000000 : ℝ)) (alpha := (963108013783/575600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1980834157/10000000000 : ℝ)*X 0 0+(5462992789/10000000000 : ℝ)*X 0 1+(1039522257/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361488209/10000000000 : ℝ)*X 1 0+(-16542981/78125000 : ℝ)*X 1 1+(5197611267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1340371993/2500000000 : ℝ)*X 2 0+(1039522307/2000000000 : ℝ)*X 2 1+(-211750153/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269056861/625000000 : ℝ)*X 0 0+(4028598579/10000000000 : ℝ)*X 0 1+(1149573309/2500000000 : ℝ)*X 0 2+(269056861/625000000 : ℝ)*X 1 0+(4028598579/10000000000 : ℝ)*X 1 1+(1149573309/2500000000 : ℝ)*X 1 2+(269056861/625000000 : ℝ)*X 2 0+(4028598579/10000000000 : ℝ)*X 2 1+(1149573309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1980883489/10000000000 : ℝ)*X 0 0+(5199162399/10000000000 : ℝ)*X 0 1+(1365357213/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292619023/10000000000 : ℝ)*X 1 0+(-926842299/5000000000 : ℝ)*X 1 1+(5461428573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292620451/10000000000 : ℝ)*X 2 0+(5461428549/10000000000 : ℝ)*X 2 1+(-1853682663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305016869/10000000000 : ℝ)*X 0 0+(574370489/1250000000 : ℝ)*X 0 1+(2015977707/5000000000 : ℝ)*X 0 2+(4305016869/10000000000 : ℝ)*X 1 0+(574370489/1250000000 : ℝ)*X 1 1+(2015977707/5000000000 : ℝ)*X 1 2+(4305016869/10000000000 : ℝ)*X 2 0+(574370489/1250000000 : ℝ)*X 2 1+(2015977707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1408_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4083591335526991268033286363/359750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235959841/12500000000000 : ℝ)*(base19) + (748389301/50000000000000 : ℝ)*(base23) + (30068543/25000000000000 : ℝ)*(lower2) + (81273739/25000000000000 : ℝ)*(upper3) + (72314047/50000000000000 : ℝ)*(upper5) + (1380888891850729/50000000000000 : ℝ)*(major0) + (1380888891850729/50000000000000 : ℝ)*(major1) + (1380888891850729/50000000000000 : ℝ)*(major2) + (942046294695851/25000000000000 : ℝ)*(sp0) + (1884102536771271/50000000000000 : ℝ)*(sp1) + (942051366110667/25000000000000 : ℝ)*(sp2) + (87766809878651/5000000000000 : ℝ)*(sp3) + (21782437867/100000000000000 : ℝ)*(sp4) + (12030235549/100000000000000 : ℝ)*(sp7) + (175534822780857/10000000000000 : ℝ)*(f.failure) + (376820696122127/10000000000000 : ℝ)*(f.sum) + (164833706285907/14390000000000000000000000000 : ℝ)*base65 + (2311528812216037121/719500000000000000000000000000000 : ℝ)*base68 + (2121832416660462879/719500000000000000000000000000000 : ℝ)*base69 + (8208623225904962879/719500000000000000000000000000000 : ℝ)*base71 + (83791684069127/14390000000000000000000000000 : ℝ)*base73 + (15635080194537121/719500000000000000000000000000000 : ℝ)*base76 + (7220964123953962879/719500000000000000000000000000000 : ℝ)*base77 + (1258674299609462879/719500000000000000000000000000000 : ℝ)*base79 + (130629946117067/14390000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1013291/1000000000000000000000 : ℝ)*base90 + (1013291/1000000000000000000000 : ℝ)*base92 + (1013291/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (454396039980844686059426481/89937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286747609/50000000000000 : ℝ)*(base19) + (2485619017/100000000000000 : ℝ)*(base23) + (44730517/100000000000000 : ℝ)*(lower2) + (19238063/12500000000000 : ℝ)*(upper3) + (246183663/100000000000000 : ℝ)*(lower4) + (6780039/25000000000000 : ℝ)*(upper5) + (698636662760877/25000000000000 : ℝ)*(major0) + (698636662760877/25000000000000 : ℝ)*(major1) + (698636662760877/25000000000000 : ℝ)*(major2) + (38636046401/100000000000000 : ℝ)*(sp2) + (238307341342097/6250000000000 : ℝ)*(sp4) + (1906458443989167/50000000000000 : ℝ)*(sp5) + (1906438169904067/50000000000000 : ℝ)*(sp6) + (888087836100839/50000000000000 : ℝ)*(sp7) + (888087836100839/50000000000000 : ℝ)*(f.failure) + (238307341342097/6250000000000 : ℝ)*(f.sum) + (2445027355161/7195000000000000000000000000 : ℝ)*base65 + (2133512736712591173/359750000000000000000000000000000 : ℝ)*base68 + (1228558522179591173/359750000000000000000000000000000 : ℝ)*base70 + (2744777732942591173/359750000000000000000000000000000 : ℝ)*base72 + (20366179741911/7195000000000000000000000000 : ℝ)*base73 + (575545746490091173/359750000000000000000000000000000 : ℝ)*base76 + (1039903960798408827/359750000000000000000000000000000 : ℝ)*base77 + (749008333329341173/359750000000000000000000000000000 : ℝ)*base80 + (20373621415291/7195000000000000000000000000 : ℝ)*base81 + (39796043/5000000000000000000000 : ℝ)*base89 + (39796043/5000000000000000000000 : ℝ)*base91 + (39796043/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1408_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4747/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2563/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7933/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1408_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1408_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2563/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7933/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1408_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1408_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1408_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4367/1024 : ℝ) ≤ p) (hpb : p ≤ (273/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157335037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2563/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7933/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1408_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
